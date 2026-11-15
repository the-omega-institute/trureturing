/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Construction
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Construction
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Construction.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Sequence
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Sequence

/-!
# Constructing circuits in a selected physical operation language

A circuit contains only its actual construction tree. Its type fixes the gate
model, granted oracle access and full physical layout. Every constructor keeps
those indices coherent; parallel execution additionally requires disjoint
physical subsystems. Operators and resource projections are not input fields.
-/

namespace QuantumAlg

/-- One model-relative construction on a fixed physical layout. -/
public structure UnitaryCircuit (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (layout : QuantumLayout count) where
  private mk ::
  /-- The actual construction tree, observable without supplying separate semantics or costs. -/
  sequence : UnitarySequence gates oracles layout

namespace UnitaryCircuit

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- Execute the zero-event identity on the complete supplied layout. -/
public def identity (gates : GateModel) (oracles : OracleModel) {count : Nat}
    (layout : QuantumLayout count) : UnitaryCircuit gates oracles layout :=
  ⟨.id layout⟩

/-- Execute one model-owned native or query application. -/
public def ofLeaf (leaf : UnitaryLeaf gates oracles layout) :
    UnitaryCircuit gates oracles layout := ⟨.leaf leaf⟩

/-- Execute a native token on its certified physical placement. -/
public def native (application : GateModel.Application gates layout) :
    UnitaryCircuit gates oracles layout := ofLeaf (.gate application)


/-- Sequential composition keeps the same language and actual physical systems. -/
public def seq (left right : UnitaryCircuit gates oracles layout) :
    UnitaryCircuit gates oracles layout := ⟨.seq left.sequence right.sequence⟩

/-- Extend an actual construction by identity on every complementary wire. -/
public def embed {small large : Nat} {source : QuantumLayout small}
    {target : QuantumLayout large} (placement : QuantumLayout.Embedding source target)
    (body : UnitaryCircuit gates oracles source) : UnitaryCircuit gates oracles target :=
  ⟨.embed placement body.sequence⟩

/-- Execute two constructions in parallel on certified disjoint physical subsystems. -/
public def parallel {leftCount rightCount count : Nat}
    {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}
    {layout : QuantumLayout count} (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (leftPlacement : QuantumLayout.Embedding leftLayout layout)
    (rightPlacement : QuantumLayout.Embedding rightLayout layout)
    (disjoint : Disjoint leftPlacement.selection rightPlacement.selection) :
    UnitaryCircuit gates oracles layout :=
  ⟨.parallel left.sequence right.sequence leftPlacement rightPlacement disjoint⟩


end UnitaryCircuit

end QuantumAlg
