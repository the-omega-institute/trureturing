/- GID: D5/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Util/FinPow/BinaryBasis
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
Original file: QuantumAlg/Util/FinPow/BinaryBasis.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Util.FinPow
public import Mathlib.Logic.Equiv.Defs
import all D5.S3.Quantum.FourierCircuit.Util.FinPow

/-!
# Big-endian finite binary coordinates

The first coordinate is the most significant bit. The explicit equivalence
connects a vector of two-valued coordinates to its existing finite binary
label, without changing the wire order or introducing padding coordinates.
-/

namespace QuantumAlg.BinaryBasis

/-- Encode finite binary coordinates in the library's big-endian order. -/
@[expose] public def bigEndianEquiv (width : Nat) : (Fin width → Fin 2) ≃ Fin (2 ^ width) where
  toFun basis := ⟨Nat.ofBits (fun index => finTwoEquiv (basis index.rev)),
    Nat.ofBits_lt_two_pow _⟩
  invFun label := fun index => finTwoEquiv.symm (label.val.testBit index.rev.val)
  left_inv basis := by
    funext index
    apply finTwoEquiv.injective
    simp only [Equiv.apply_symm_apply]
    rw [Nat.testBit_ofBits_lt]
    · exact congrArg (fun position => finTwoEquiv (basis position)) (Fin.rev_rev index)
    · exact index.rev.isLt
  right_inv label := by
    apply Fin.val_injective
    change Nat.ofBits (fun index : Fin width =>
      finTwoEquiv (finTwoEquiv.symm (label.val.testBit index.rev.rev.val))) = label.val
    simp only [Equiv.apply_symm_apply, Fin.rev_rev, Nat.ofBits_testBit,
      Nat.mod_eq_of_lt label.isLt]

/-- The logical wire index selects the corresponding most-significant-first bit. -/
public lemma bigEndianEquiv_bit (width : Nat) (basis : Fin width → Fin 2) (index : Fin width) :
    (bigEndianEquiv width basis).val.testBit index.rev.val = finTwoEquiv (basis index) := by
  change (Nat.ofBits fun position : Fin width => finTwoEquiv (basis position.rev)).testBit
    index.rev.val = finTwoEquiv (basis index)
  rw [Nat.testBit_ofBits_lt]
  · exact congrArg (fun position => finTwoEquiv (basis position)) (Fin.rev_rev index)
  · exact index.rev.isLt


end QuantumAlg.BinaryBasis
