/- GID: D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm/Permutation
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
Original file: QuantumAlg/Components/GateModel/Algorithm/Permutation.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.GateModel.Algorithm
import all D5.S3.Quantum.FourierCircuit.Components.GateModel.Algorithm
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Operator
import all D5.S3.Quantum.FourierCircuit.Components.QubitPrimitive.Operator
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary.Permutation
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Util.FinPow.BinaryBasis

/-!
# Native reversible gates on their declared argument values

The default model's actual X, CNOT and Toffoli operators have exact permutation
semantics on their original arguments. These proofs use the fixed big-endian
interpretation already owned by the model, including full operator phase.
-/

namespace QuantumAlg.AlgorithmGate

noncomputable section

/-- The row permutation of the model's fixed two-qubit CNOT. -/
@[expose]
public def cnotPermutation : Equiv.Perm (QuantumSignature.qubits 2).Basis :=
  (((QuantumSignature.qubitsIndexEquiv 2).trans (Equiv.swap 2 3)).trans
    (QuantumSignature.qubitsIndexEquiv 2).symm)

/-- This permutation interprets the actual native token with exact phase. -/
public lemma cnot_operator_ofPerm :
    model.operator .cnot = UnitaryOperator.ofPerm cnotPermutation := by
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm
    (UnitaryOperator.ofPerm (Equiv.swap 2 3)) = _
  exact UnitaryOperator.reindex_ofPerm (QuantumSignature.qubitsIndexEquiv 2).symm _

/-- CNOT acts on the ordered control and target values, with addition in `Fin 2`. -/
public lemma cnotPermutation_pair (control target : Fin 2) :
    cnotPermutation ![control, target] = ![control, control + target] := by
  fin_cases control <;> fin_cases target
  all_goals
    funext index
    fin_cases index <;> rfl


end

end QuantumAlg.AlgorithmGate
