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
Library/Quantum/qudeleap2026qft.md.
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
import all D5.S3.Quantum.FourierCircuit.Core.Base.Depth.Expr
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
rations classicalOracles)) :=
  circuit.sequence.eventDepth operations classicalOracles
t) : Nat :=
  DepthExpr.depthEval duration circuit.eventDepth
 : Nat :=
  DepthExpr.queryDepthEval focus circuit.eventDepth
ircuit : UnitaryCircuit gates oracles layout) : Nat :=
  circuit.sequence.macroTrace.count name
leton event)
    (circuit.eventDepth operations classicalOracles)
_eventCost circuit.sequence operations classicalOracles

/-- Forgetting order in the actual native trace yields exactly the circuit's event ledger. -/
@[simp] public lemma ofList_eventTrace_eq_eventCost
    (circuit : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool.ofList (circuit.eventTrace operations classicalOracles) =
      circuit.eventCost operations classicalOracles :=
  UnitarySequence.ofList_eventTrace_eq_eventCost circuit.sequence operations classicalOracles
 HilbertVector layout.register :=
  (circuit.matrix environment).applyVec state
ter) : NormalizedVector layout.register :=
  (circuit.matrix environment).apply state

variable (environment : oracles.Interpretation)

@[simp] lemma identity_matrix : ((identity gates oracles layout).matrix environment) = 1 := by rfl

@[simp] lemma identity_eventCost : (identity gates oracles layout).eventCost = 0 := by rfl
l
l
identity gates oracles layout).evaluatedEventDepth duration = 0 := by
  rfl
ofLeaf leaf).matrix environment) = leaf.operator environment := by rfl
    (ofLeaf leaf).eventCost = ResourcePool.singleton leaf.event := by rfl

@[simp] public lemma native_matrix (application : GateModel.Application gates layout) :
    ((native (oracles := oracles) application).matrix environment) = application.operator := by rfl
 ResourcePool.singleton (model := .quantum gates oracles) (.gate application.coordinate) := by
  rfl
eventTrace =
      [.gate application.coordinate] := by rfl
 duration (.gate application.coordinate) := by
  rfl
environment =
      application.operator environment := by rfl
   (.oracle application.coordinate) := by
  rfl
 duration (.oracle application.coordinate) := by
  rfl

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
yVec ((left.matrix environment).applyVec state) index
  rw [UnitaryOperator.mul_applyVec]

@[simp] lemma seq_eventCost (left right : UnitaryCircuit gates oracles layout) :
    (seq left right).eventCost = left.eventCost + right.eventCost := by rfl
 :
    (seq left right).eventTrace = left.eventTrace ++ right.eventTrace := by rfl

    (seq left right).eventDepth = .seq left.eventDepth right.eventDepth := by rfl
ation + right.evaluatedEventDepth duration := by rfl
 left.eventCost + right.eventCost := by
  rfl
 max (left.evaluatedEventDepth duration) (right.evaluatedEventDepth duration) := by
  rfl
     body.matrix environment ^ repetitions := by rfl
.eventCost = repetitions • body.eventCost := by rfl
 (List.replicate repetitions body.eventTrace).flatten := by
  rfl
th = .iterate repetitions body.eventDepth := by rfl

@[simp] lemma macroCall_matrix (name : String) (body : UnitaryCircuit gates oracles layout) :
    ((macroCall name body).matrix environment) = (body.matrix environment) := by rfl
aryCircuit gates oracles layout) :
    (macroCall name body).eventCost = body.eventCost := by rfl
ryCircuit gates oracles layout) :
    (macroCall name body).eventTrace = body.eventTrace := by rfl
ryCircuit gates oracles layout) :
    (macroCall name body).eventDepth = body.eventDepth := by rfl
 body.evaluatedEventDepth duration := by
  rfl
dd_comm]
  · simp [macroCount, macroCall, UnitarySequence.macroTrace, same]
umulated next => next * accumulated) (start.matrix environment) := by rfl
rt.eventCost + ∑ index, (step index).eventCost := by rfl
   (fun index => (step index).eventDepth) := by rfl
   ∑ index, (step index).evaluatedEventDepth duration := by
  rfl

end

end QuantumAlg.UnitaryCircuit
