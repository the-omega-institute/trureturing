/- GID: D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis/Pair
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Fourier/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Util/FinPow/BinaryBasis/Pair.lean.
Authors: QudeLeap Team
-/

module

import all D5.S3.Quantum.FourierCircuit.Util.FinPow.BinaryBasis
import all D5.S3.Quantum.FourierCircuit.Util.FinPow.BitReverse
import all D5.S3.Quantum.FourierCircuit.Util.FinPow
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Leading-bit decomposition of big-endian coordinates

Prepending one binary coordinate places it above all tail bits in the encoded
natural label. The pairing convention agrees with the original finite product.
-/

namespace QuantumAlg.BinaryBasis

lemma bigEndianEquiv_cons_value (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) :
    (bigEndianEquiv (n + 1) (Fin.cons head tail)).val =
      (bigEndianEquiv n tail).val + 2 ^ n * head.val := by
  change Nat.ofBits (fun index : Fin (n + 1) =>
      finTwoEquiv (Fin.cons (α := fun _ => Fin 2) head tail index.rev)) =
    Nat.ofBits (fun index : Fin n => finTwoEquiv (tail index.rev)) + 2 ^ n * head.val
  rw [nat_ofBits_succ_last]
  congr 1
  · apply congrArg Nat.ofBits
    funext index
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.cons_succ]
  · simp only [Fin.rev_last, Fin.cons_zero]
    congr 1
    fin_cases head <;> rfl

lemma bigEndianEquiv_cons_pair (n : Nat) (head : Fin 2) (tail : Fin n → Fin 2) :
    bigEndianEquiv (n + 1) (Fin.cons head tail) =
      qftPairEquiv n (head, bigEndianEquiv n tail) := by
  apply Fin.ext
  rw [bigEndianEquiv_cons_value, qftPairEquiv_apply_val]

end QuantumAlg.BinaryBasis
