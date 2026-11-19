/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Leaf
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Leaf
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Leaf.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
public import D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Placement
public import D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.Event
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Placement

/-!
# Native gates and independently granted queries

A leaf contains one model-owned instance applied to its actual physical wires.
There is no independent operator, event label or resource witness. Gate tokens
and oracle queries inhabit separate declaration-owned types; neither can be
created by relabeling an unsupported operation.
-/

namespace QuantumAlg

/-- The only atomic unitary operations in a selected execution language. -/
public inductive UnitaryLeaf (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (layout : QuantumLayout count) where
  /-- A gate from the selected native model on its dimension-correct wires. -/
  | gate (application : GateModel.Application gates layout)
  /-- A query explicitly granted by the independent oracle declaration. -/
  | oracle (application : OracleModel.Application oracles layout)

namespace UnitaryLeaf

variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}

/-- The single native event fixed by the actual applied instance. -/
@[expose]
public def event (leaf : UnitaryLeaf gates oracles layout)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    Resource.Event (.quantum gates oracles operations classicalOracles) :=
  match leaf with
  | .gate application => .gate application.coordinate
  | .oracle application => .oracle application.coordinate

/-- Unitary semantics come from the same native or query instance. -/
@[expose]
public noncomputable def operator (environment : oracles.Interpretation) :
    UnitaryLeaf gates oracles layout →
    UnitaryOperator layout.register
  | .gate application => application.operator
  | .oracle application => application.operator environment


end UnitaryLeaf

end QuantumAlg
