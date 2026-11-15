/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Model
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/Model
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
Original file: QuantumAlg/Core/Base/Gate/Model.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
public import D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator

/-!
# Model-relative elementary gates

A gate model interprets its own parameterized tokens on fixed physical system
signatures. A decidable resource coordinate may group several tokens, but it
does not determine their operators or erase their parameters. Physical gate
occurrences store only a token and a legal placement; their operator is always
derived from that same model interpretation.

No distinguished gate alphabet or gate-parameter equality is required here.
Concrete model definitions belong with their named component operators.
-/

namespace QuantumAlg

/-- An elementary-gate language with fixed physical and unitary semantics. -/
public structure GateModel where
  /-- Actual gate instances, including all semantic parameters. -/
  Token : Type
  /-- Decidable accounting coordinates may group parameterized gate instances. -/
  Coordinate : Type
  /-- Equality is needed for counts, not for arbitrary gate parameters. -/
  coordinateDecidableEq : DecidableEq Coordinate
  /-- Ordered dimensions of the systems touched by a token. -/
  signature : Token → QuantumSignature
  /-- The operator is fixed by the token on its declared local systems. -/
  operator : (token : Token) → UnitaryOperator (signature token).register
  /-- The accounting coordinate emitted by one token occurrence. -/
  coordinate : Token → Coordinate

attribute [instance] GateModel.coordinateDecidableEq

namespace GateModel

/-- One occurrence of a gate from a specific model. No independently supplied
operator, event count, depth or space claim is stored here. -/
public structure Occurrence (model : GateModel) where
  /-- Actual model-owned gate instance. -/
  token : model.Token
  /-- Actual physical systems, with matching dimensions and distinct identities. -/
  placement : (model.signature token).Placement

namespace Occurrence

/-- The event coordinate follows the actual token. -/
@[expose]
public def coordinate {model : GateModel} (gate : Occurrence model) : model.Coordinate :=
  model.coordinate gate.token

/-- Unitary action on the actual local layout, transported only through its
certified coordinate-wise dimension equalities. -/
@[expose]
public noncomputable def operator {model : GateModel} (gate : Occurrence model) :
    UnitaryOperator gate.placement.layout.register :=
  UnitaryOperator.reindex gate.placement.indexEquiv.symm (model.operator gate.token)


end Occurrence


end GateModel

end QuantumAlg
