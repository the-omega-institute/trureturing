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
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Components/Gates/Swap.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
import all D5.S3.Quantum.FourierCircuit.Components.Gates.Construction
public import D5.S3.Quantum.FourierCircuit.Components.GateModel.Algorithm.Permutation
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Canonical
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Canonical
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Permutation
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement.Permutation
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Util.FinPow.BinaryBasis
public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Realization
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit

/-!
# Exact SWAP from three actual native CNOT applications

The target exchanges the two computational-basis coordinates independently of
the implementation. The default-model construction uses CNOT in the forward,
backward and forward directions. Its macro annotation retains this entire
expansion and therefore its native events and sequential dependency depth.
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

private abbrev backward : GateModel.Application AlgorithmGate.model layout :=
  cnotApplication layout 1 0 (by decide) rfl rfl

private def backwardPermutation : Equiv.Perm layout.Basis :=
  backward.liftPermutation AlgorithmGate.cnotPermutation

private lemma backward_pair (left right : Fin 2) :
    backwardPermutation ![left, right] = ![left + right, right] := by
  apply (backward.liftPermutation_eq_iff AlgorithmGate.cnotPermutation _ _).mpr
  constructor
  · have selected (first second : Fin 2) :
        (backward.basisEquiv ![first, second]).1 = ![second, first] := by
      funext index
      fin_cases index <;> apply Fin.ext <;> rfl
    have action := AlgorithmGate.cnotPermutation_pair right left
    rw [add_comm right left] at action
    exact ((congrArg AlgorithmGate.cnotPermutation (selected left right)).trans action).trans
      (selected (left + right) right).symm
  · funext position
    have covered (index : Fin 2) : index ∈ backward.embedding.selection := by
      fin_cases index <;> decide
    exact False.elim ((Finset.mem_compl.mp position.property) (covered position.val))

private lemma native_permutation_word :
    (AlgorithmGate.cnotPermutation.trans backwardPermutation).trans
      AlgorithmGate.cnotPermutation = permutation := by
  have pair (left right : Fin 2) :
      AlgorithmGate.cnotPermutation
        (backwardPermutation (AlgorithmGate.cnotPermutation ![left, right])) =
          permutation ![left, right] := by
    rw [AlgorithmGate.cnotPermutation_pair, backward_pair,
      AlgorithmGate.cnotPermutation_pair, swap_permutation_pair]
    fin_cases left <;> fin_cases right <;> rfl
  apply Equiv.ext
  intro basis
  have coordinates : basis = ![basis (0 : Fin 2), basis (1 : Fin 2)] := by
    funext index
    fin_cases index <;> rfl
  rw [coordinates]
  change AlgorithmGate.cnotPermutation
    (backwardPermutation (AlgorithmGate.cnotPermutation
      ![basis (0 : Fin 2), basis (1 : Fin 2)])) = _
  exact pair _ _

/-- Execute the full forward/backward/forward CNOT word as one descriptive macro. -/
public def circuit (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout :=
  let forward : UnitaryCircuit AlgorithmGate.model oracles layout :=
    UnitaryCircuit.native (GateModel.Application.canonical AlgorithmGate.model .cnot)
  UnitaryCircuit.macroCall "swap"
    ((forward.seq (UnitaryCircuit.native backward)).seq forward)

/-- The three actual CNOTs realize the independent SWAP operator with exact phase. -/
public lemma swap_circuit_matrix (oracles : OracleModel) (environment : oracles.Interpretation) :
    ((circuit oracles).matrix environment) = operator := by
  simp only [circuit, UnitaryCircuit.macroCall_matrix, UnitaryCircuit.seq_matrix,
    UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator,
    AlgorithmGate.cnot_operator_ofPerm,
    backward.operator_ofPerm AlgorithmGate.cnotPermutation AlgorithmGate.cnot_operator_ofPerm]
  simp only [UnitaryOperator.ofPerm_mul]
  exact congrArg UnitaryOperator.ofPerm native_permutation_word


end

end QuantumAlg.Gate.Swap
