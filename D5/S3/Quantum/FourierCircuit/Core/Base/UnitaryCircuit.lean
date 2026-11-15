/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Construction
public import D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Construction
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Sequence
import all D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.ResourcePool
import all D5.S3.Quantum.FourierCircuit.Core.Base.State.Normalized

/-!
# Semantics and accounting of physical model-relative circuits

Every observation comes from the actual construction stored by the circuit.
The type fixes the gate model, declared oracle access and full physical layout.
Native events include expanded macro bodies, while macro names support separate
statistics on that same execution. No label-to-cost interpretation is accepted.
-/

namespace QuantumAlg.UnitaryCircuit

open scoped BigOperators

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Exact, metadata-free unitary semantics of the actual construction. -/
public def matrix (circuit : UnitaryCircuit gates oracles layout)
    (environment : oracles.Interpretation) : UnitaryOperator layout.register :=
  circuit.sequence.toUnitary environment

/-- Ordered native occurrences, including every actual macro expansion. -/
public def eventTrace (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    List (Resource.Event (.quantum gates oracles operations classicalOracles)) :=
  circuit.sequence.eventTrace operations classicalOracles

/-- Literal model-relative event multiplicities from the same construction. -/
public def eventCost (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum gates oracles operations classicalOracles) :=
  circuit.sequence.eventCost operations classicalOracles


/-- Forgetting order in the actual native trace yields exactly the circuit's event ledger. -/
@[simp] public lemma ofList_eventTrace_eq_eventCost
    (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool.ofList (circuit.eventTrace operations classicalOracles) =
      circuit.eventCost operations classicalOracles :=
  UnitarySequence.ofList_eventTrace_eq_eventCost circuit.sequence operations classicalOracles


variable (environment : oracles.Interpretation)

@[simp] lemma identity_matrix : ((identity gates oracles layout).matrix environment) = 1 := by rfl

@[simp] lemma identity_eventCost : (identity gates oracles layout).eventCost = 0 := by rfl


@[simp] public lemma native_matrix (application : GateModel.Application gates layout) :
    ((native (oracles := oracles) application).matrix environment) = application.operator := by rfl


@[simp] lemma seq_matrix (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).matrix environment =
      right.matrix environment * left.matrix environment := by rfl

/-- Parallel syntax denotes the product of the two actual lifted operators. -/
@[simp] public lemma parallel_matrix_raw {leftCount rightCount count : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {layout : QuantumLayout count} (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    ((parallel left right leftPlacement rightPlacement disjoint).matrix environment) =
      rightPlacement.liftOperator (right.matrix environment) *
        leftPlacement.liftOperator (left.matrix environment) := by
  rfl


@[simp] lemma seq_eventCost (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).eventCost = left.eventCost + right.eventCost := by rfl
end

end QuantumAlg.UnitaryCircuit
