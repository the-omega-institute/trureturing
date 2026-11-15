/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle/Signature
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle/Signature
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
Original file: QuantumAlg/Core/Base/Classical/Oracle/Signature.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Classical.Value
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Classical service interfaces and interpretations

A service interface fixes the available queries, operand and result shapes,
finite hidden-state carrier and native coordinates. Its interpretation is a
separate transition law, supplied only to execution. Initial hidden state is
an actual input and is never selected again by an ordinary query.
-/

namespace QuantumAlg

/-- One classical service's query interface, without a transition law. -/
public structure ClassicalOracleSignature where
  /-- Exactly the granted parameterized queries. -/
  Query : Type
  /-- Declaration-owned native query coordinates. -/
  Coordinate : Type
  /-- Equality is required only for counting coordinates. -/
  coordinateDecidableEq : DecidableEq Coordinate
  /-- Finite persistent state, inaccessible through caller storage references. -/
  HiddenState : Type
  /-- The interface fixes the finite state carrier at its public configuration. -/
  stateFintype : Fintype HiddenState
  /-- Operand shape selected by the granted query. -/
  inputShape : Query → CShape
  /-- Visible result shape selected by the same query. -/
  outputShape : Query → CShape
  /-- Native event emitted by an occurrence of this query. -/
  coordinate : Query → Coordinate

attribute [instance] ClassicalOracleSignature.coordinateDecidableEq
attribute [instance] ClassicalOracleSignature.stateFintype

namespace ClassicalOracleSignature


end ClassicalOracleSignature

end QuantumAlg
