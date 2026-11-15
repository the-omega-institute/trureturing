/- GID: D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator
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
Original file: QuantumAlg/Components/QubitPrimitive/Operator.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.WireAddress

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary

/-!
# Addressed reversible qubit operators

The common X/CNOT/Toffoli basis actions, physical wire selections and unitary
operators are independent of circuit syntax and its native resource model.
-/

section

namespace QuantumAlg

noncomputable section

/-- Wire-addressed declarations for the common reversible qubit primitives. -/
public inductive QubitPrimitive (n : Nat) where
  /-- Flip one addressed qubit. -/
  | x (target : Fin n)
  /-- Flip a target qubit when one distinct control qubit is set. -/
  | cnot (control target : Fin n) (hct : control ≠ target)
  /-- Flip a target qubit when two pairwise-distinct controls are set. -/
  | toffoli (controlA controlB target : Fin n)
      (hab : controlA ≠ controlB) (ha : controlA ≠ target)
      (hb : controlB ≠ target)

namespace QubitPrimitive

/-- Classical computational-basis action of one primitive declaration. -/
public def applyLabel {n : Nat} : QubitPrimitive n → Fin (2 ^ n) → Fin (2 ^ n)
  | .x target, label => WireAddress.flipBit target label
  | .cnot control target _hct, label => WireAddress.cnotMap control target label
  | .toffoli controlA controlB target _hab _ha _hb, label =>
      WireAddress.toffoliMap controlA controlB target label

/-- Certified basis permutation of one primitive declaration. -/
def perm {n : Nat} : QubitPrimitive n → Equiv.Perm (Fin (2 ^ n))
  | .x target => WireAddress.xPerm target
  | .cnot control target hct => WireAddress.cnotPerm control target hct
  | .toffoli controlA controlB target hab ha hb =>
      WireAddress.toffoliPerm controlA controlB target hab ha hb

@[simp]
lemma perm_apply {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) : primitive.perm label = primitive.applyLabel label := by
  cases primitive <;> rfl


/-- Canonical unitary operator of one addressed primitive declaration. -/
public def operator {n : Nat} (primitive : QubitPrimitive n) :
    UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofPerm primitive.perm.symm

@[simp]
public lemma operator_apply_ket {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) :
    primitive.operator.apply (NormalizedVector.ket label) =
      NormalizedVector.ket (primitive.applyLabel label) := by
  unfold operator
  rw [UnitaryOperator.ofPerm_apply_ket]
  change NormalizedVector.ket (R := Qubits n) (primitive.perm label) = _
  rw [perm_apply]

end QubitPrimitive

end

end QuantumAlg

end
