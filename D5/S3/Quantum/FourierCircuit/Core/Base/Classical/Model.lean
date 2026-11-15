/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Model
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Classical/Model
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
Original file: QuantumAlg/Core/Base/Classical/Model.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Classical.Value
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Model-relative classical native operations

A native declaration fixes each token's operand shapes, probability semantics
and accounting coordinate. Deterministic instructions use point distributions.
Randomized instructions have normalized finite-valued outcomes; their result
distribution is part of the declaration, not an argument supplied at a call.

These declarations do not place storage, grant oracle access or attach a bit
complexity to a word operation. Actual placement and interpretation are separate
boundaries using the same declared token.
-/

namespace QuantumAlg

/-- A classical native language with fixed typed semantics and resource coordinates. -/
public structure ClassicalOpModel where
  /-- Actual native-operation instances, including their semantic parameters. -/
  Token : Type
  /-- Decidable coordinates may group several parameterized operations. -/
  Coordinate : Type
  /-- Counts require equality of coordinates, not of semantic parameters. -/
  coordinateDecidableEq : DecidableEq Coordinate
  /-- Operand shape fixed by the native token. -/
  inputShape : Token → CShape
  /-- Result shape fixed by the same token. -/
  outputShape : Token → CShape
  /-- The declaration's normalized result distribution for the actual operands. -/
  evaluate : (token : Token) → (inputShape token).Value → PMF (outputShape token).Value
  /-- The native coordinate emitted by one actual token occurrence. -/
  coordinate : Token → Coordinate

attribute [instance] ClassicalOpModel.coordinateDecidableEq

namespace ClassicalOpModel

/-- The empty native grant contains no executable tokens or native coordinates. -/
@[expose, implicit_reducible]
public def empty : ClassicalOpModel where
  Token := Empty
  Coordinate := Empty
  coordinateDecidableEq := inferInstance
  inputShape token := nomatch token
  outputShape token := nomatch token
  evaluate token := nomatch token
  coordinate token := nomatch token


end ClassicalOpModel

end QuantumAlg
