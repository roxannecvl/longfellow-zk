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

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_ECDSA_VERIFY_WITH_PK_COMMITMENT_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_ECDSA_VERIFY_WITH_PK_COMMITMENT_H_

#include <array>
#include <cstddef>
#include <cstdint>

#include "circuits/ecdsa/verify_circuit.h"
#include "circuits/logic/bit_plucker.h"
#include "circuits/sha/flatsha256_circuit.h"

namespace proofs {

// Proves ECDSA verification with a *private* public key, bound to a *public*
// commitment.
//
// Public statement:
//   - commitment == SHA256( pkx_be || pky_be || rho )
//   - signature verifies for (pkx, pky, e)
//
// Private witness:
//   - pkx, pky (as field elements)
//   - pkx_be, pky_be (32-byte big-endian encodings of pkx/pky)
//   - rho (32 bytes)
//   - SHA256 internal round witnesses for the 2-block message
//   - ECDSA verification witness (includes signature)
//
// Notes:
// - The SHA preimage is fixed-length (96 bytes) so padding is constant.
// - The circuit links pkx/pky to pkx_be/pky_be by packing bits into a field
//   element and range-checking against the field modulus.
template <class LogicCircuit, class Field, class EC>
class EcdsaVerifyWithPkCommitment {
  using EltW = typename LogicCircuit::EltW;
  using Elt = typename LogicCircuit::Elt;
  using Nat = typename Field::N;
  using v8 = typename LogicCircuit::v8;
  using v64 = typename LogicCircuit::v64;
  using v256 = typename LogicCircuit::v256;

  static constexpr size_t kSHAPluckerBits = 4u;
  using Sha = FlatSHA256Circuit<LogicCircuit,
                                BitPlucker<LogicCircuit, kSHAPluckerBits>>;
  using ShaBlockWitness = typename Sha::BlockWitness;
  using Ecdsa = VerifyCircuit<LogicCircuit, Field, EC>;
  using EcdsaWitness = typename Ecdsa::Witness;

 public:
  struct Witness {
    EltW pk_x;
    EltW pk_y;

    std::array<v8, 32> pkx_be;
    std::array<v8, 32> pky_be;
    std::array<v8, 32> rho;

    std::array<ShaBlockWitness, 2> sha_bw;
    EcdsaWitness sig;

    void input(const LogicCircuit& lc) {
      pk_x = lc.eltw_input();
      pk_y = lc.eltw_input();

      for (size_t i = 0; i < 32; ++i) {
        pkx_be[i] = lc.template vinput<8>();
      }
      for (size_t i = 0; i < 32; ++i) {
        pky_be[i] = lc.template vinput<8>();
      }
      for (size_t i = 0; i < 32; ++i) {
        rho[i] = lc.template vinput<8>();
      }

      for (size_t b = 0; b < 2; ++b) {
        sha_bw[b].input(lc);
      }

      sig.input(lc);
    }
  };

  EcdsaVerifyWithPkCommitment(const LogicCircuit& lc, const EC& ec,
                              const Nat& order)
      : lc_(lc), ec_(ec), order_(order), sha_(lc_), ecdsa_(lc_, ec_, order_) {
    // Cache modulus bits for range checks when packing bytes to field elements.
    for (size_t i = 0; i < 256; ++i) {
      bits_p_[i] = lc_.bit(lc_.f_.m_.bit(i));
    }
  }

  // Public inputs:
  //   - e: message scalar interpreted as a field element
  //   - commitment: SHA256(pkx_be || pky_be || rho)
  void assert_valid(EltW e, const v256& commitment, const Witness& w) const {
    assert_bytes_be_matches_field_element(w.pkx_be, w.pk_x);
    assert_bytes_be_matches_field_element(w.pky_be, w.pk_y);

    std::array<v8, 128> sha_in;
    build_commitment_preimage(sha_in, w);
    auto nb = lc_.template vbit<8>(2);
    sha_.assert_message_hash(/*max=*/2, nb, sha_in.data(), commitment,
                             w.sha_bw.data());

    ecdsa_.verify_signature3(w.pk_x, w.pk_y, e, w.sig);
  }

 private:
  v256 bytes_be_to_v256(const std::array<v8, 32>& buf_be) const {
    // v256 is little-endian (bit 0 is LSB). The input bytes are big-endian.
    v256 bits;
    for (size_t i = 0; i < 256; ++i) {
      bits[i] = buf_be[31 - (i / 8)][i % 8];
    }
    return bits;
  }

  void assert_bytes_be_matches_field_element(const std::array<v8, 32>& buf_be,
                                             EltW x) const {
    v256 bits = bytes_be_to_v256(buf_be);
    lc_.vassert_is_bit(bits);

    // Ensure the byte encoding is canonical (no wraparound mod p).
    lc_.assert1(lc_.vlt(&bits, bits_p_));

    // Pack bits into the field element and compare.
    EltW packed = lc_.konst(lc_.zero());
    Elt pow2 = lc_.one();
    for (size_t i = 0; i < 256; ++i) {
      packed = lc_.axpy(&packed, pow2, lc_.eval(bits[i]));
      lc_.f_.add(pow2, pow2);
    }
    lc_.assert_eq(&packed, x);
  }

  void build_commitment_preimage(std::array<v8, 128>& out,
                                 const Witness& w) const {
    // Message = pkx_be || pky_be || rho, length 96 bytes.
    // Padding (SHA256): append 0x80, then zeros, then 64-bit length (768)
    // big-endian.
    size_t i = 0;
    for (size_t j = 0; j < 32; ++j) out[i++] = w.pkx_be[j];
    for (size_t j = 0; j < 32; ++j) out[i++] = w.pky_be[j];
    for (size_t j = 0; j < 32; ++j) out[i++] = w.rho[j];

    out[i++] = lc_.template vbit<8>(0x80);
    while (i < 120) {
      out[i++] = lc_.template vbit<8>(0);
    }
    // 96 bytes * 8 = 768 bits = 0x0000000000000300
    out[i++] = lc_.template vbit<8>(0x00);
    out[i++] = lc_.template vbit<8>(0x00);
    out[i++] = lc_.template vbit<8>(0x00);
    out[i++] = lc_.template vbit<8>(0x00);
    out[i++] = lc_.template vbit<8>(0x00);
    out[i++] = lc_.template vbit<8>(0x00);
    out[i++] = lc_.template vbit<8>(0x03);
    out[i++] = lc_.template vbit<8>(0x00);
  }

  const LogicCircuit& lc_;
  const EC& ec_;
  const Nat& order_;
  Sha sha_;
  Ecdsa ecdsa_;
  v256 bits_p_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_ECDSA_VERIFY_WITH_PK_COMMITMENT_H_
