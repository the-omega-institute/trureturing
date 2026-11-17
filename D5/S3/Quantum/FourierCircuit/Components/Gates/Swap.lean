/- GID: D5/S3/Quantum/FourierCircuit/Components/Gates/Swap
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Components/Gates/Swap
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
Original file: QuantumAlg/Components/Gates/Swap.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary.Permutation
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary.Permutation
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature

/-!
# Independent exact SWAP operator

The target exchanges the two computational-basis coordinates on every input.
-/

namespace QuantumAlg.Gate.Swap

noncomputable section

/-- The two physical qubits on which the local construction runs. -/
@[expose, implicit_reducible]
public def layout : QuantumLayout 2 := (QuantumSignature.qubits 2).canonicalPlacement.layout

/-- The independent two-qubit exchange permutation, in the fixed big-endian basis. -/
@[expose]
public def permutation : Equiv.Perm layout.Basis :=
  ((QuantumSignature.qubitsIndexEquiv 2).trans (Equiv.swap 1 2)).trans
    (QuantumSignature.qubitsIndexEquiv 2).symm

/-- The target exchanges both values, without an assumption on either input. -/
public lemma swap_permutation_pair (left right : Fin 2) :
    permutation ![left, right] = ![right, left] := by
  fin_cases left <;> fin_cases right
  all_goals
    funext index
    fin_cases index <;> rfl

/-- The target acts coherently by exchanging the two basis coordinates. -/
@[expose]
public def operator : UnitaryOperator layout.register := UnitaryOperator.ofPerm permutation

end

end QuantumAlg.Gate.Swap
