/- GID: D5/S3/Quantum/FourierCircuit/Util/ResidueEncoding
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Util/ResidueEncoding
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Util/ResidueEncoding.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
import Mathlib.Data.ZMod.Basic

/-!
# Binary residue-register encoding

This module records the quantum-free convention for using a binary register
label `Fin (2^n)` as storage for residues modulo `N`. The register label follows
the library-wide big-endian computational-basis convention; the arithmetic
content here is only the natural-number label and its reduction modulo `N`.

This is the register-level convention behind the reversible modular arithmetic
networks that store residues in computational-basis registers before composing
modular addition, multiplication, and exponentiation [VBE95,
9511018.tex:107-115, 276-286] [Bea02, arxivfact.tex:97-118].
-/

section

namespace QuantumAlg
ister_fits : N ≤ 2 ^ n

namespace BinaryResidueEncoding
 E.modulus_pos
  x.val < N
lid x) :=
  inferInstanceAs (Decidable (x.val < N))
lus_pos
  (x.val : ZMod N)
lt_of_lt_of_le (ZMod.val_lt z) E.register_fits⟩
aryResidueEncoding N n) (z : ZMod N) :
    (E.encode z).val = z.val := rfl
:= by
  simp [decode, ZMod.val_natCast]
⟩
  simpa [IsValid, encode] using ZMod.val_lt z
ne_of_gt E.modulus_pos⟩
  simp [decode, encode]
code_encode right, h]
Nat.mod_eq_of_lt hx
  rw [encode_val, decode_val, hmod]

end BinaryResidueEncoding

end QuantumAlg

end
