// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include "algebra/convolution.h"
#include "algebra/fp2.h"
#include "algebra/reed_solomon.h"

#include "arrays/dense.h"
#include "circuits/compiler/circuit_dump.h"
#include "circuits/compiler/compiler.h"
#include "circuits/ecdsa/verify_with_pk_commitment.h"
#include "circuits/ecdsa/verify_witness.h"
#include "circuits/logic/bit_plucker_encoder.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/sha/flatsha256_witness.h"
#include "ec/p256.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

using Field = Fp256Base;
using Nat = Field::N;
using Elt = Field::Elt;

static constexpr size_t kSHAPluckerBits = 4u;

// Extract SHA256 digest bytes (big-endian) from the final block witness.
std::array<uint8_t, 32> digest_from_h1(
    const FlatSHA256Witness::BlockWitness& bw_last) {
  std::array<uint8_t, 32> out{};
  for (size_t i = 0; i < 8; ++i) {
    uint32_t w = bw_last.h1[i];
    out[4 * i + 0] = static_cast<uint8_t>((w >> 24) & 0xff);
    out[4 * i + 1] = static_cast<uint8_t>((w >> 16) & 0xff);
    out[4 * i + 2] = static_cast<uint8_t>((w >> 8) & 0xff);
    out[4 * i + 3] = static_cast<uint8_t>((w >> 0) & 0xff);
  }
  return out;
}

std::array<uint8_t, 32> field_element_to_be_bytes(const Field& F,
                                                  const Elt& x) {
  std::array<uint8_t, 32> le{};
  std::array<uint8_t, 32> be{};
  F.to_bytes_field(le.data(), x);
  for (size_t i = 0; i < 32; ++i) {
    be[i] = le[31 - i];
  }
  return be;
}

std::unique_ptr<Circuit<Field>> make_circuit(const Field& f) {
  using CompilerBackend = CompilerBackend<Field>;
  using LogicCircuit = Logic<Field, CompilerBackend>;
  using v256 = typename LogicCircuit::v256;
  using EltW = typename LogicCircuit::EltW;

  QuadCircuit<Field> Q(f);
  const CompilerBackend cbk(&Q);
  const LogicCircuit lc(&cbk, f);

  // Public inputs.
  EltW e_pub = lc.eltw_input();
  v256 commitment_pub = lc.template vinput<256>();

  // Private inputs.
  Q.private_input();
  EcdsaVerifyWithPkCommitment<LogicCircuit, Field, P256> circ(lc, p256,
                                                              n256_order);
  typename EcdsaVerifyWithPkCommitment<LogicCircuit, Field, P256>::Witness w;
  w.input(lc);

  circ.assert_valid(e_pub, commitment_pub, w);

  auto circuit = Q.mkcircuit(/*nc=*/1);
  dump_info("ecdsa verify + pk commitment", Q);
  return circuit;
}

void fill_input(Dense<Field>& W, const Field& f, bool prover,
        const std::array<uint8_t, 32>& rho) {
  // Use the first fixed ECDSA test vector from verify_test.cc.
  const char pkx_hex[] =
      "0x88903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaaf686c8f9ff5e7c6368d9c";
  const char pky_hex[] =
      "0xeb8341fc38bb802138498d5f4c03733f457ebbafd0b2fe38e6f58626767f9e75";
  const char e_hex[] =
      "0x2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae";
  const char r_hex[] =
      "0xc71bcbfb28bbe06299a225f057797aaf5f22669e90475de5f64176b2612671";
  const char s_hex[] =
      "0x42ad2f2ec7b6e91360b53427690dddfe578c10d8cf480a66a6c2410ff4f6dd40";

  const Elt pk_x = f.of_string(pkx_hex);
  const Elt pk_y = f.of_string(pky_hex);
  const Nat e_nat(e_hex);
  const Nat r_nat(r_hex);
  const Nat s_nat(s_hex);
  const Elt e_field = f.to_montgomery(e_nat);

  // Compute pk byte encodings (big-endian) and SHA witness for
  // SHA256(pkx_be || pky_be || rho).
  std::array<uint8_t, 32> pkx_be = field_element_to_be_bytes(f, pk_x);
  std::array<uint8_t, 32> pky_be = field_element_to_be_bytes(f, pk_y);

  std::array<uint8_t, 96> msg{};
  for (size_t i = 0; i < 32; ++i) msg[i] = pkx_be[i];
  for (size_t i = 0; i < 32; ++i) msg[32 + i] = pky_be[i];
  for (size_t i = 0; i < 32; ++i) msg[64 + i] = rho[i];

  uint8_t numb = 0;
  std::array<uint8_t, 128> sha_in{};
  std::array<FlatSHA256Witness::BlockWitness, 2> sha_bw{};
  FlatSHA256Witness::transform_and_witness_message(/*n=*/msg.size(), msg.data(),
                                                   /*max=*/2, numb,
                                                   sha_in.data(),
                                                   sha_bw.data());
  ASSERT_EQ(numb, 2u);
  std::array<uint8_t, 32> digest = digest_from_h1(sha_bw[numb - 1]);

  // ECDSA verification witness (includes signature).
  VerifyWitness3<P256, Fp256Scalar> ecdsa_w(p256_scalar, p256);
  bool ok = ecdsa_w.compute_witness(pk_x, pk_y, e_nat, r_nat, s_nat);
  ASSERT_TRUE(ok);

  DenseFiller<Field> filler(W);
  filler.push_back(f.one());

  // Public: e (field element)
  filler.push_back(e_field);

  // Public: commitment digest bits (v256 layout expected by FlatSHA256Circuit)
  for (size_t j = 0; j < 256; ++j) {
    const uint8_t bit =
        (digest[(255 - j) / 8] >> (j % 8)) & 1 ? 1 : 0;
    filler.push_back(f.of_scalar(bit));
  }

  // Private: pk_x, pk_y
  filler.push_back(pk_x);
  filler.push_back(pk_y);

  // Private: pkx_be, pky_be, rho bytes (each as v8 = 8 bit inputs)
  for (size_t i = 0; i < 32; ++i) filler.push_back(pkx_be[i], 8, f);
  for (size_t i = 0; i < 32; ++i) filler.push_back(pky_be[i], 8, f);
  for (size_t i = 0; i < 32; ++i) filler.push_back(rho[i], 8, f);

  // Private: SHA block witnesses (packed)
  if (prover) {
    BitPluckerEncoder<Field, kSHAPluckerBits> BPENC(f);
    for (size_t b = 0; b < 2; ++b) {
      for (size_t k = 0; k < 48; ++k) {
        filler.push_back(BPENC.mkpacked_v32(sha_bw[b].outw[k]));
      }
      for (size_t k = 0; k < 64; ++k) {
        filler.push_back(BPENC.mkpacked_v32(sha_bw[b].oute[k]));
        filler.push_back(BPENC.mkpacked_v32(sha_bw[b].outa[k]));
      }
      for (size_t k = 0; k < 8; ++k) {
        filler.push_back(BPENC.mkpacked_v32(sha_bw[b].h1[k]));
      }
    }

    // Private: ECDSA witness (includes signature)
    ecdsa_w.fill_witness(filler);
  }
}

void fill_public_input(Dense<Field>& pub, const Field& f,
                       const std::array<uint8_t, 32>& rho) {
  const char e_hex[] =
      "0x2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae";
  const Nat e_nat(e_hex);
  const Elt e_field = f.to_montgomery(e_nat);

  // pk used in verify_test.cc's first vector.
  const char pkx_hex[] =
      "0x88903e4e1339bde78dd5b3d7baf3efdd72eb5bf5aaaf686c8f9ff5e7c6368d9c";
  const char pky_hex[] =
      "0xeb8341fc38bb802138498d5f4c03733f457ebbafd0b2fe38e6f58626767f9e75";
  const Elt pk_x = f.of_string(pkx_hex);
  const Elt pk_y = f.of_string(pky_hex);

  std::array<uint8_t, 32> pkx_be = field_element_to_be_bytes(f, pk_x);
  std::array<uint8_t, 32> pky_be = field_element_to_be_bytes(f, pk_y);

  std::array<uint8_t, 96> msg{};
  for (size_t i = 0; i < 32; ++i) msg[i] = pkx_be[i];
  for (size_t i = 0; i < 32; ++i) msg[32 + i] = pky_be[i];
  for (size_t i = 0; i < 32; ++i) msg[64 + i] = rho[i];

  uint8_t numb = 0;
  std::array<uint8_t, 128> sha_in{};
  std::array<FlatSHA256Witness::BlockWitness, 2> sha_bw{};
  FlatSHA256Witness::transform_and_witness_message(/*n=*/msg.size(), msg.data(),
                                                   /*max=*/2, numb,
                                                   sha_in.data(),
                                                   sha_bw.data());
  ASSERT_EQ(numb, 2u);
  std::array<uint8_t, 32> digest = digest_from_h1(sha_bw[numb - 1]);

  DenseFiller<Field> filler(pub);
  filler.push_back(f.one());
  filler.push_back(e_field);
  for (size_t j = 0; j < 256; ++j) {
    const uint8_t bit =
        (digest[(255 - j) / 8] >> (j % 8)) & 1 ? 1 : 0;
    filler.push_back(f.of_scalar(bit));
  }
}

TEST(ECDSA, ProverVerifier_PrivatePkWithCommitment) {
  set_log_level(INFO);

  std::unique_ptr<Circuit<Field>> circuit = make_circuit(p256_base);
  {
    const size_t npub = circuit->npub_in;
    const size_t nin = circuit->ninputs;
    log(INFO, "Inputs: npub_in=%zu, ninputs=%zu, nprivate=%zu", npub, nin,
        nin >= npub ? (nin - npub) : 0);
    log(INFO,
        "Public inputs are: 1 (constant), e (field element), commitment (256 bits)"
    );
    EXPECT_EQ(npub, 1u + 1u + 256u);
  }

  using f2_p256 = Fp2<Fp256Base>;
  using Elt2 = f2_p256::Elt;
  using FftExtConvolutionFactory = FFTExtConvolutionFactory<Fp256Base, f2_p256>;
  using RSFactory = ReedSolomonFactory<Fp256Base, FftExtConvolutionFactory>;
  const f2_p256 p256_2(p256_base);

  // Root of unity for the f_p256^2 extension field.
  static constexpr char kRootX[] =
      "112649224146410281873500457609690258373018840430489408729223714171582664"
      "680802";
  static constexpr char kRootY[] =
      "840879943585409076957404614278186605601821689971823787493130182544504602"
      "12908";

  const Elt2 omega = p256_2.of_string(kRootX, kRootY);
  const FftExtConvolutionFactory fft_b(p256_base, p256_2, omega, 1ull << 31);
  const RSFactory rsf(fft_b, p256_base);

  SecureRandomEngine rng;
  ZkVerifier<Field, RSFactory> verifier(*circuit, rsf, /*logv=*/4, /*lambda=*/128,
                                        p256_base);

  // Run multiple proofs with different rho (so different public commitment)
  // without recompiling the circuit.
  static constexpr size_t kNumProofs = 5;
  double prover_ms_sum = 0.0;
  double verifier_ms_sum = 0.0;
  for (size_t i = 0; i < kNumProofs; ++i) {
    std::array<uint8_t, 32> rho{};
    for (size_t j = 0; j < rho.size(); ++j) {
      rho[j] = static_cast<uint8_t>(j ^ (13u * i));
    }

    auto W = Dense<Field>(/*n0=*/1, circuit->ninputs);
    fill_input(W, p256_base, /*prover=*/true, rho);

    ZkProof<Field> zkpr(*circuit, /*logv=*/4, /*lambda=*/128);
    {
      Transcript tp((uint8_t*)"testing", 7);
      // Note: we intentionally create a fresh prover per proof.
      // Reusing a ZkProver across multiple proofs can retain internal pad
      // state (via witness_ growth) and lead to invalid proofs.
      ZkProver<Field, RSFactory> prover(*circuit, p256_base, rsf);
      const auto start = std::chrono::steady_clock::now();
      prover.commit(zkpr, W, tp, rng);
      ASSERT_TRUE(prover.prove(zkpr, W, tp));
      const auto end = std::chrono::steady_clock::now();
      const double ms =
          std::chrono::duration<double, std::milli>(end - start).count();
      prover_ms_sum += ms;
      log(INFO, "ZK prover time (commit+prove) [rho#%zu]: %.3f ms", i, ms);

      // Proof size as bytes sent prover -> verifier.
      // We report both the estimated upper bound and the actual serialized size.
      std::vector<uint8_t> proof_bytes;
      proof_bytes.reserve(zkpr.size());
      zkpr.write(proof_bytes, p256_base);
      log(INFO,
          "ZK proof size [rho#%zu]: estimated<=%zu B, serialized=%zu B",
          i, zkpr.size(), proof_bytes.size());
    }

    auto pub = Dense<Field>(/*n0=*/1, circuit->npub_in);
    fill_public_input(pub, p256_base, rho);
    {
      Transcript tv((uint8_t*)"testing", 7);
      const auto start = std::chrono::steady_clock::now();
      verifier.recv_commitment(zkpr, tv);
      ASSERT_TRUE(verifier.verify(zkpr, pub, tv));
      const auto end = std::chrono::steady_clock::now();
      const double ms =
          std::chrono::duration<double, std::milli>(end - start).count();
      verifier_ms_sum += ms;
      log(INFO, "ZK verifier time [rho#%zu]: %.3f ms", i, ms);
    }
  }

  log(INFO, "ZK prover avg over %zu proofs: %.3f ms", kNumProofs,
      prover_ms_sum / static_cast<double>(kNumProofs));
  log(INFO, "ZK verifier avg over %zu proofs: %.3f ms", kNumProofs,
      verifier_ms_sum / static_cast<double>(kNumProofs));
}

}  // namespace
}  // namespace proofs
