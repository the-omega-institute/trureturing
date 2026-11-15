/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Physical.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Construction
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Sequence
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Relabeling
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Relabeling
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary.Reindex
import all D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Placement

/-!
# Relocating the complete physical construction

An injective physical-address map relocates every actual wire, gate occurrence
and query occurrence in the same construction tree. Logical positions,
dimensions and basis values stay fixed. Disjoint subsystems remain disjoint;
native instances, exact operators, resource counts, dependencies and macro
observations are preserved. The new circuit's type records the relocated layout.
-/

namespace QuantumAlg

namespace QuantumLayout.Embedding

/-- Relocate source and target wires with the same injective physical-address map. -/
def relabel {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}
    (placement : Embedding source target) (physical : Nat ↪ Nat) :
    Embedding (source.relabel physical) (target.relabel physical) where
  position := placement.position
  wire_eq index := congrArg (QuantumWire.relabel physical) (placement.wire_eq index)

/-- The same local operator acts on the same coordinate values after physical relocation. -/
@[simp] lemma liftOperator_relabel {small large : Nat}
    {source : QuantumLayout small} {target : QuantumLayout large}
    (placement : Embedding source target) (physical : Nat ↪ Nat)
    (operator : UnitaryOperator source.register) :
    (placement.relabel physical).liftOperator operator = placement.liftOperator operator := by
  rfl

end QuantumLayout.Embedding

namespace GateModel.Application

/-- Relocate the actual native token and its complete physical embedding together. -/
def relabel {model : GateModel} {count : Nat} {layout : QuantumLayout count}
    (application : Application model layout) (physical : Nat ↪ Nat) :
    Application model (layout.relabel physical) where
  occurrence :=
    { token := application.occurrence.token
      placement :=
        { layout := application.occurrence.placement.layout.relabel physical
          dimension_eq := application.occurrence.placement.dimension_eq } }
  embedding := application.embedding.relabel physical

end GateModel.Application

namespace OracleModel.Application

/-- Relocation preserves the actual query instance and cannot grant a new access form. -/
def relabel {model : OracleModel} {count : Nat} {layout : QuantumLayout count}
    (application : Application model layout) (physical : Nat ↪ Nat) :
    Application model (layout.relabel physical) where
  occurrence :=
    { query := application.occurrence.query
      placement :=
        { layout := application.occurrence.placement.layout.relabel physical
          dimension_eq := application.occurrence.placement.dimension_eq } }
  embedding := application.embedding.relabel physical

end OracleModel.Application

namespace UnitaryLeaf

/-- Relocate the actual leaf without changing its declared operation instance. -/
def relabel {gates : GateModel} {oracles : OracleModel} {count : Nat}
    {layout : QuantumLayout count} (leaf : UnitaryLeaf gates oracles layout)
    (physical : Nat ↪ Nat) : UnitaryLeaf gates oracles (layout.relabel physical) :=
  match leaf with
  | .gate application => .gate (application.relabel physical)
  | .oracle application => .oracle (application.relabel physical)

end UnitaryLeaf

namespace UnitarySequence

variable {gates : GateModel} {oracles : OracleModel}

/-- Relocate every leaf and intermediate subsystem with one injective physical-address map. -/
def relabel (physical : Nat ↪ Nat) : {count : Nat} → {layout : QuantumLayout count} →
    UnitarySequence gates oracles layout →
      UnitarySequence gates oracles (layout.relabel physical)
  | _, layout, .id _ => .id (layout.relabel physical)
  | _, _, .leaf atom => .leaf (atom.relabel physical)
  | _, _, .seq left right => .seq (left.relabel physical) (right.relabel physical)
  | _, _, .embed placement body => .embed (placement.relabel physical) (body.relabel physical)
  | _, _, .parallel left right leftPlacement rightPlacement disjoint =>
      .parallel (left.relabel physical) (right.relabel physical)
        (leftPlacement.relabel physical) (rightPlacement.relabel physical) disjoint
  | _, _, .iterate repetitions body => .iterate repetitions (body.relabel physical)
  | _, _, .indexedProduct label steps start step =>
      .indexedProduct label steps (start.relabel physical)
        (fun index => (step index).relabel physical)
  | _, _, .macroCall name body => .macroCall name (body.relabel physical)

variable {count : Nat} {layout : QuantumLayout count}

/-- Logical operators are unchanged because relocation preserves every coordinate value. -/
@[simp] lemma toUnitary_relabel (physical : Nat ↪ Nat)
    (sequence : UnitarySequence gates oracles layout) (environment : oracles.Interpretation) :
    ((sequence.relabel physical).toUnitary environment) = (sequence.toUnitary environment) := by
  induction sequence with
  | id => rfl
  | leaf atom => cases atom <;> rfl
  | seq left right leftIH rightIH =>
      simp only [relabel, toUnitary, leftIH, rightIH]
      rfl
  | embed placement body bodyIH =>
      simp only [relabel, toUnitary, QuantumLayout.Embedding.liftOperator_relabel, bodyIH]
      rfl
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp only [relabel, toUnitary, QuantumLayout.Embedding.liftOperator_relabel, leftIH, rightIH]
      rfl
  | iterate repetitions body bodyIH =>
      simp only [relabel, toUnitary, bodyIH]
      rfl
  | indexedProduct label steps start step startIH stepIH =>
      simp only [relabel, toUnitary, startIH, stepIH]
      rfl
  | macroCall name body bodyIH => simpa [relabel, toUnitary] using bodyIH

/-- Relocation retains each original native and query occurrence in execution order. -/
@[simp] lemma eventTrace_relabel (physical : Nat ↪ Nat)
    (sequence : UnitarySequence gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (sequence.relabel physical).eventTrace operations classicalOracles =
      sequence.eventTrace operations classicalOracles := by
  induction sequence with
  | id => rfl
  | leaf atom => cases atom <;> rfl
  | seq left right leftIH rightIH => simp [relabel, eventTrace, leftIH, rightIH]
  | embed placement body bodyIH => simpa [relabel, eventTrace] using bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [relabel, eventTrace, leftIH, rightIH]
  | iterate repetitions body bodyIH => simp [relabel, eventTrace, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [relabel, eventTrace, startIH, stepIH]
  | macroCall name body bodyIH => simpa [relabel, eventTrace] using bodyIH


end UnitarySequence

namespace UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Relocate the actual circuit and expose its new physical layout in the result type. -/
public def relabel (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) :
    UnitaryCircuit gates oracles (layout.relabel physical) :=
  ⟨circuit.sequence.relabel physical⟩

private lemma relabel_matrix_internal (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (environment : oracles.Interpretation) : ((circuit.relabel
      physical).matrix environment) = (circuit.matrix environment) :=
  UnitarySequence.toUnitary_relabel physical circuit.sequence environment

@[simp] public lemma relabel_matrix (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (environment : oracles.Interpretation) : ((circuit.relabel
      physical).matrix environment) = (circuit.matrix environment) :=
  relabel_matrix_internal circuit physical environment


private lemma relabel_eventTrace_internal
    (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventTrace operations classicalOracles =
      circuit.eventTrace operations classicalOracles :=
  UnitarySequence.eventTrace_relabel physical circuit.sequence operations classicalOracles

@[simp] public lemma relabel_eventTrace (circuit : UnitaryCircuit gates oracles layout)
    (physical : Nat ↪ Nat) (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    (circuit.relabel physical).eventTrace operations classicalOracles =
      circuit.eventTrace operations classicalOracles :=
  relabel_eventTrace_internal circuit physical operations classicalOracles


end UnitaryCircuit

end QuantumAlg
