/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Sequence
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Sequence.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Leaf
public import D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.ResourcePool
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Leaf
import all D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.ResourcePool
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator

/-!
# Model-relative unitary constructions on physical layouts

One syntax tree determines the exact operator, native events, event depth and
macro statistics. A macro contains its expansion; its descriptive name does not
select semantics or costs. Parallel branches are embedded on disjoint physical
systems. Embedding adds only untouched spectator wires. Inverse and controlled
operations must be implemented by actual words in the selected language.
-/

namespace QuantumAlg

open scoped BigOperators

/-- Unitary syntax indexed by its native language, granted queries and physical layout. -/
public inductive UnitarySequence (gates : GateModel) (oracles : OracleModel) :
    {count : Nat} → QuantumLayout count → Type 1 where
  /-- The zero-event identity on the complete physical layout. -/
  | id {count : Nat} (layout : QuantumLayout count) : UnitarySequence gates oracles layout
  /-- One actual native gate or declared query application. -/
  | leaf {count : Nat} {layout : QuantumLayout count}
      (value : UnitaryLeaf gates oracles layout) : UnitarySequence gates oracles layout
  /-- Execute two constructions in order on the same physical systems. -/
  | seq {count : Nat} {layout : QuantumLayout count}
      (left right : UnitarySequence gates oracles layout) : UnitarySequence gates oracles layout
  /-- Place a construction on the same physical wires within a larger layout. -/
  | embed {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}
      (placement : QuantumLayout.Embedding source target)
      (body : UnitarySequence gates oracles source) : UnitarySequence gates oracles target
  /-- Parallel execution is permitted only on physically disjoint embedded subsystems. -/
  | parallel {leftCount rightCount count : Nat}
      {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
      {layout : QuantumLayout count}
      (left : UnitarySequence gates oracles leftLayout)
      (right : UnitarySequence gates oracles rightLayout)
      (leftPlacement : QuantumLayout.Embedding leftLayout layout)
      (rightPlacement : QuantumLayout.Embedding rightLayout layout)
      (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
      UnitarySequence gates oracles layout
  /-- Symbolic exact repetition of the actual body. -/
  | iterate {count : Nat} {layout : QuantumLayout count}
      (repetitions : Nat) (body : UnitarySequence gates oracles layout) :
      UnitarySequence gates oracles layout
  /-- A start construction followed by an indexed family in increasing index order. -/
  | indexedProduct {count : Nat} {layout : QuantumLayout count}
      (label : String) (steps : Nat) (start : UnitarySequence gates oracles layout)
      (step : Fin steps → UnitarySequence gates oracles layout) :
      UnitarySequence gates oracles layout
  /-- A descriptive macro name and its sole actual implementation. -/
  | macroCall {count : Nat} {layout : QuantumLayout count}
      (name : String) (body : UnitarySequence gates oracles layout) :
      UnitarySequence gates oracles layout

namespace UnitarySequence

variable {gates : GateModel} {oracles : OracleModel}

noncomputable section

/-- Interpret the actual tree as a certified unitary. Later operations multiply on the left. -/
@[expose]
public def toUnitary (environment : oracles.Interpretation) :
    {count : Nat} → {layout : QuantumLayout count} →
    UnitarySequence gates oracles layout → UnitaryOperator layout.register
  | _, _, .id _ => 1
  | _, _, .leaf atom => (atom.operator environment)
  | _, _, .seq left right => (right.toUnitary environment) * (left.toUnitary environment)
  | _, _, .embed placement body => placement.liftOperator (body.toUnitary environment)
  | _, _, .parallel left right leftPlacement rightPlacement _ =>
      rightPlacement.liftOperator (right.toUnitary environment) *
        leftPlacement.liftOperator (left.toUnitary environment)
  | _, _, .iterate repetitions body => (body.toUnitary environment) ^ repetitions
  | _, _, .indexedProduct _ _ start step =>
      (List.ofFn (fun index => ((step index).toUnitary environment))).foldl
        (fun accumulated next => next * accumulated) (start.toUnitary environment)
  | _, _, .macroCall _ body => (body.toUnitary environment)

/-- Native execution occurrences, retaining sequential order and every macro expansion. -/
@[expose]
public def eventTrace {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    List (Resource.Event (.quantum gates oracles operations classicalOracles)) :=
  match sequence with
  | .id _ => []
  | .leaf atom => [atom.event operations classicalOracles]
  | .seq left right =>
      left.eventTrace operations classicalOracles ++ right.eventTrace operations classicalOracles
  | .embed _ body => body.eventTrace operations classicalOracles
  | .parallel left right _ _ _ =>
      left.eventTrace operations classicalOracles ++ right.eventTrace operations classicalOracles
  | .iterate repetitions body =>
      (List.replicate repetitions (body.eventTrace operations classicalOracles)).flatten
  | .indexedProduct _ _ start step =>
      start.eventTrace operations classicalOracles ++
        (List.ofFn fun index => (step index).eventTrace operations classicalOracles).flatten
  | .macroCall _ body => body.eventTrace operations classicalOracles

/-- Symbolic native multiplicities from the same construction, without enumerating repeats. -/
@[expose]
public def eventCost {count : Nat} {layout : QuantumLayout count}
    (sequence : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool (.quantum gates oracles operations classicalOracles) :=
  match sequence with
  | .id _ => 0
  | .leaf atom => ResourcePool.singleton (atom.event operations classicalOracles)
  | .seq left right =>
      left.eventCost operations classicalOracles + right.eventCost operations classicalOracles
  | .embed _ body => body.eventCost operations classicalOracles
  | .parallel left right _ _ _ =>
      left.eventCost operations classicalOracles + right.eventCost operations classicalOracles
  | .iterate repetitions body => repetitions • (body.eventCost operations classicalOracles)
  | .indexedProduct _ _ start step =>
      start.eventCost operations classicalOracles +
        ∑ index, (step index).eventCost operations classicalOracles
  | .macroCall _ body => body.eventCost operations classicalOracles


variable {count : Nat} {layout : QuantumLayout count}

variable (environment : oracles.Interpretation)


private lemma ofList_flatten_eventTraces {model : ExecutionModel}
    (traces : List (List (Resource.Event model))) :
    ResourcePool.ofList traces.flatten = (traces.map ResourcePool.ofList).sum := by
  induction traces with
  | nil => rfl
  | cons trace traces ih => simp [ih]

/-- Forgetting event order gives exactly the symbolic native multiplicity ledger. -/
@[simp] public lemma ofList_eventTrace_eq_eventCost
    (sequence : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    ResourcePool.ofList (sequence.eventTrace operations classicalOracles) =
      sequence.eventCost operations classicalOracles := by
  induction sequence with
  | id => rfl
  | leaf atom => rfl
  | seq left right leftIH rightIH => simp [eventTrace, eventCost, leftIH, rightIH]
  | embed placement body bodyIH => simpa [eventTrace, eventCost] using bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [eventTrace, eventCost, leftIH, rightIH]
  | iterate repetitions body bodyIH =>
      rw [eventTrace, eventCost, ofList_flatten_eventTraces]
      simp [bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      rw [eventTrace, eventCost, ResourcePool.ofList_append, ofList_flatten_eventTraces]
      simp [startIH, stepIH, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  | macroCall name body bodyIH => simpa [eventTrace, eventCost] using bodyIH

end

end UnitarySequence

end QuantumAlg
