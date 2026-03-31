#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <chrono>
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

namespace proofs {

using Field = Fp256Base;
using Nat256 = Field::N;
using Elt = Field::Elt;

static constexpr size_t kSHAPluckerBits = 4u;

static std::string strip_0x(std::string_view s) {
  if (s.size() >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
    return std::string(s.substr(2));
  }
  return std::string(s);
}

static bool is_hex_char(char c) {
  return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') ||
         (c >= 'A' && c <= 'F');
}

static uint8_t hex_to_nibble(char c) {
  if (c >= '0' && c <= '9') return static_cast<uint8_t>(c - '0');
  if (c >= 'a' && c <= 'f') return static_cast<uint8_t>(10 + (c - 'a'));
  if (c >= 'A' && c <= 'F') return static_cast<uint8_t>(10 + (c - 'A'));
  throw std::runtime_error("invalid hex");
}

static std::vector<uint8_t> parse_hex_bytes(std::string_view hex_in) {
  std::string hex = strip_0x(hex_in);
  if (hex.size() % 2 != 0) throw std::runtime_error("hex must have even length");
  for (char c : hex) {
    if (!is_hex_char(c)) throw std::runtime_error("hex contains non-hex characters");
  }
  std::vector<uint8_t> out(hex.size() / 2);
  for (size_t i = 0; i < out.size(); i++) {
    out[i] = static_cast<uint8_t>((hex_to_nibble(hex[2 * i]) << 4) |
                                  hex_to_nibble(hex[2 * i + 1]));
  }
  return out;
}

static std::array<uint8_t, 32> parse_hex_32(std::string_view hex_in) {
  auto v = parse_hex_bytes(hex_in);
  if (v.size() != 32) throw std::runtime_error("expected 32-byte hex value");
  std::array<uint8_t, 32> out{};
  std::memcpy(out.data(), v.data(), 32);
  return out;
}

static std::optional<std::string> arg_value(int argc, char** argv,
                                            std::string_view key) {
  const std::string prefix = std::string(key) + "=";
  for (int i = 1; i < argc; i++) {
    std::string_view a(argv[i]);
    if (a == key) {
      if (i + 1 >= argc)
        throw std::runtime_error("missing value after " + std::string(key));
      return std::string(argv[i + 1]);
    }
    if (a.rfind(prefix, 0) == 0) {
      return std::string(a.substr(prefix.size()));
    }
  }
  return std::nullopt;
}

static void usage(const char* prog) {
  std::cerr
      << "Usage:\n"
      << "  " << prog
      << " --pkx=0x.. --pky=0x.. --rho=0x.. --e=0x.. --r=0x.. --s=0x.. "
         "[--expected-commitment=0x..]\n";
}

struct Inputs {
  std::string pkx_hex;
  std::string pky_hex;
  std::array<uint8_t, 32> rho;
  std::string e_hex;
  std::string r_hex;
  std::string s_hex;
  std::optional<std::array<uint8_t, 32>> expected_commitment;
};

static Inputs parse_inputs(int argc, char** argv) {
  Inputs in;
  auto pkx = arg_value(argc, argv, "--pkx");
  auto pky = arg_value(argc, argv, "--pky");
  auto rho = arg_value(argc, argv, "--rho");
  auto e = arg_value(argc, argv, "--e");
  auto r = arg_value(argc, argv, "--r");
  auto s = arg_value(argc, argv, "--s");
  auto exp = arg_value(argc, argv, "--expected-commitment");

  if (!pkx || !pky || !rho || !e || !r || !s) {
    usage(argv[0]);
    throw std::runtime_error("missing required arguments");
  }

  in.pkx_hex = *pkx;
  in.pky_hex = *pky;
  in.rho = parse_hex_32(*rho);
  in.e_hex = *e;
  in.r_hex = *r;
  in.s_hex = *s;
  if (exp) in.expected_commitment = parse_hex_32(*exp);
  return in;
}

// Extract SHA256 digest bytes (big-endian) from the final block witness.
static std::array<uint8_t, 32> digest_from_h1(
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

static std::array<uint8_t, 32> field_element_to_be_bytes(const Field& F,
                                                         const Elt& x) {
  std::array<uint8_t, 32> le{};
  std::array<uint8_t, 32> be{};
  F.to_bytes_field(le.data(), x);
  for (size_t i = 0; i < 32; ++i) {
    be[i] = le[31 - i];
  }
  return be;
}

static std::unique_ptr<Circuit<Field>> make_circuit(const Field& f) {
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
  return circuit;
}

static std::array<uint8_t, 32> fill_input(Dense<Field>& W, const Field& f,
                                          bool prover,
                                          const Inputs& in) {
  const auto pk_x_maybe = f.of_untrusted_string(in.pkx_hex.c_str());
  const auto pk_y_maybe = f.of_untrusted_string(in.pky_hex.c_str());
  const auto e_nat_maybe = Nat256::of_untrusted_string(in.e_hex.c_str());
  const auto r_nat_maybe = Nat256::of_untrusted_string(in.r_hex.c_str());
  const auto s_nat_maybe = Nat256::of_untrusted_string(in.s_hex.c_str());
  if (!pk_x_maybe.has_value() || !pk_y_maybe.has_value() ||
      !e_nat_maybe.has_value() || !r_nat_maybe.has_value() ||
      !s_nat_maybe.has_value()) {
    throw std::runtime_error("failed to parse pk/e/r/s as hex");
  }
  const Elt pk_x = pk_x_maybe.value();
  const Elt pk_y = pk_y_maybe.value();
  const Nat256 e_nat = e_nat_maybe.value();
  const Nat256 r_nat = r_nat_maybe.value();
  const Nat256 s_nat = s_nat_maybe.value();
  const Elt e_field = f.to_montgomery(e_nat);

  // Compute pk byte encodings (big-endian) and SHA witness for
  // SHA256(pkx_be || pky_be || rho).
  std::array<uint8_t, 32> pkx_be = field_element_to_be_bytes(f, pk_x);
  std::array<uint8_t, 32> pky_be = field_element_to_be_bytes(f, pk_y);

  std::array<uint8_t, 96> msg{};
  for (size_t i = 0; i < 32; ++i) msg[i] = pkx_be[i];
  for (size_t i = 0; i < 32; ++i) msg[32 + i] = pky_be[i];
  for (size_t i = 0; i < 32; ++i) msg[64 + i] = in.rho[i];

  uint8_t numb = 0;
  std::array<uint8_t, 128> sha_in{};
  std::array<FlatSHA256Witness::BlockWitness, 2> sha_bw{};
  FlatSHA256Witness::transform_and_witness_message(/*n=*/msg.size(), msg.data(),
                                                   /*max=*/2, numb,
                                                   sha_in.data(),
                                                   sha_bw.data());
  if (numb != 2u) throw std::runtime_error("unexpected SHA witness blocks");
  std::array<uint8_t, 32> digest = digest_from_h1(sha_bw[numb - 1]);

  // ECDSA verification witness (includes signature).
  VerifyWitness3<P256, Fp256Scalar> ecdsa_w(p256_scalar, p256);
  bool ok = ecdsa_w.compute_witness(pk_x, pk_y, e_nat, r_nat, s_nat);
  if (!ok) throw std::runtime_error("ECDSA witness computation failed");

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
  for (size_t i = 0; i < 32; ++i) filler.push_back(in.rho[i], 8, f);

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
    ecdsa_w.fill_witness(filler);
  }

  return digest;
}

static void fill_public_input(Dense<Field>& pub, const Field& f,
                              const Inputs& in) {
  const auto e_nat_maybe = Nat256::of_untrusted_string(in.e_hex.c_str());
  const auto pk_x_maybe = f.of_untrusted_string(in.pkx_hex.c_str());
  const auto pk_y_maybe = f.of_untrusted_string(in.pky_hex.c_str());
  if (!e_nat_maybe.has_value() || !pk_x_maybe.has_value() ||
      !pk_y_maybe.has_value()) {
    throw std::runtime_error("failed to parse public inputs as hex");
  }
  const Nat256 e_nat = e_nat_maybe.value();
  const Elt e_field = f.to_montgomery(e_nat);

  const Elt pk_x = pk_x_maybe.value();
  const Elt pk_y = pk_y_maybe.value();

  std::array<uint8_t, 32> pkx_be = field_element_to_be_bytes(f, pk_x);
  std::array<uint8_t, 32> pky_be = field_element_to_be_bytes(f, pk_y);

  std::array<uint8_t, 96> msg{};
  for (size_t i = 0; i < 32; ++i) msg[i] = pkx_be[i];
  for (size_t i = 0; i < 32; ++i) msg[32 + i] = pky_be[i];
  for (size_t i = 0; i < 32; ++i) msg[64 + i] = in.rho[i];

  uint8_t numb = 0;
  std::array<uint8_t, 128> sha_in{};
  std::array<FlatSHA256Witness::BlockWitness, 2> sha_bw{};
  FlatSHA256Witness::transform_and_witness_message(/*n=*/msg.size(), msg.data(),
                                                   /*max=*/2, numb,
                                                   sha_in.data(),
                                                   sha_bw.data());
  if (numb != 2u) throw std::runtime_error("unexpected SHA witness blocks");
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

}  // namespace proofs

int main(int argc, char** argv) {
  try {
    // Keep CLI output minimal; we print explicit timings and proof size.
    proofs::set_log_level(proofs::WARNING);

    const auto in = proofs::parse_inputs(argc, argv);

    std::unique_ptr<proofs::Circuit<proofs::Fp256Base>> circuit =
      proofs::make_circuit(proofs::p256_base);

    // This mirrors verify_with_pk_commitment_test.cc's configuration.
    using f2_p256 = proofs::Fp2<proofs::Fp256Base>;
    using Elt2 = f2_p256::Elt;
    using FftExtConvolutionFactory =
        proofs::FFTExtConvolutionFactory<proofs::Fp256Base, f2_p256>;
    using RSFactory =
        proofs::ReedSolomonFactory<proofs::Fp256Base, FftExtConvolutionFactory>;
    const f2_p256 p256_2(proofs::p256_base);

    static constexpr char kRootX[] =
        "112649224146410281873500457609690258373018840430489408729223714171582664"
        "680802";
    static constexpr char kRootY[] =
        "840879943585409076957404614278186605601821689971823787493130182544504602"
        "12908";

    const Elt2 omega = p256_2.of_string(kRootX, kRootY);
    const FftExtConvolutionFactory fft_b(proofs::p256_base, p256_2, omega,
                                         1ull << 31);
    const RSFactory rsf(fft_b, proofs::p256_base);

    proofs::SecureRandomEngine rng;
    proofs::ZkVerifier<proofs::Fp256Base, RSFactory> verifier(
        *circuit, rsf, /*logv=*/4, /*lambda=*/128, proofs::p256_base);

    auto W = proofs::Dense<proofs::Fp256Base>(/*n0=*/1, circuit->ninputs);
    const auto digest = proofs::fill_input(W, proofs::p256_base,
                                           /*prover=*/true, in);

    if (in.expected_commitment.has_value() &&
        in.expected_commitment.value() != digest) {
      std::cerr << "Expected commitment != computed digest\n";
      return 2;
    }

    proofs::ZkProof<proofs::Fp256Base> zkpr(*circuit, /*logv=*/4, /*lambda=*/128);
    double prover_ms = 0.0;
    {
      proofs::Transcript tp((uint8_t*)"cli", 3);
      proofs::ZkProver<proofs::Fp256Base, RSFactory> prover(*circuit,
                                                           proofs::p256_base,
                                                           rsf);

      // Match verify_with_pk_commitment_test.cc: time commit+prove only.
      const auto start = std::chrono::steady_clock::now();
      prover.commit(zkpr, W, tp, rng);
      if (!prover.prove(zkpr, W, tp)) {
        std::cerr << "Prover failed\n";
        return 1;
      }

      const auto end = std::chrono::steady_clock::now();
      prover_ms = std::chrono::duration<double, std::milli>(end - start).count();
    }

    // Report a concrete proof size by serializing the proof.
    // This is useful for end-to-end benchmarking and for comparing against
    // other proof systems (e.g., Groth16).
    {
      std::vector<uint8_t> proof_bytes;
      proof_bytes.reserve(zkpr.size());
      zkpr.write(proof_bytes, proofs::p256_base);
      std::cout << "Longfellow proof bytes: " << proof_bytes.size() << "\n";
    }

    std::cout << "Longfellow prover ms (commit+prove): " << prover_ms << "\n";

    auto pub = proofs::Dense<proofs::Fp256Base>(/*n0=*/1, circuit->npub_in);
    proofs::fill_public_input(pub, proofs::p256_base, in);
    double verifier_ms = 0.0;
    {
      proofs::Transcript tv((uint8_t*)"cli", 3);

      // Match verify_with_pk_commitment_test.cc: time recv_commitment+verify.
      const auto start = std::chrono::steady_clock::now();
      verifier.recv_commitment(zkpr, tv);
      if (!verifier.verify(zkpr, pub, tv)) {
        std::cerr << "VERIFY FAILED\n";
        return 1;
      }

      const auto end = std::chrono::steady_clock::now();
      verifier_ms = std::chrono::duration<double, std::milli>(end - start).count();
    }

    std::cout << "Longfellow verifier ms (recv_commit+verify): " << verifier_ms << "\n";

    std::cout << "Longfellow verify_with_pk_commitment: OK\n";
    return 0;
  } catch (const std::exception& e) {
    std::cerr << "Error: " << e.what() << "\n";
    return 1;
  }
}
