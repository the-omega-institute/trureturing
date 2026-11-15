/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle
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
Original file: QuantumAlg/Core/Base/Classical/Oracle.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Classical.Oracle.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Classical.Oracle.Signature

/-!
# Declared classical services with independent interpretation

A query interface contains no stochastic transition law. An environment
interprets each atomic service separately. A sum retains both persistent states
and both interpretations, so querying one service cannot change the other.
Shared mutable access uses the same service sequentially, never a service sum.
-/

namespace QuantumAlg

/-- Fixed query interfaces with structural separation of independent services. -/
public inductive ClassicalOracleModel where
  /-- No queries and no persistent service information. -/
  | empty
  /-- One service with a fixed interface and an externally supplied interpretation. -/
  | service (signature : ClassicalOracleSignature)
  /-- Two independent services with distinct queries and persistent states. -/
  | sum (left right : ClassicalOracleModel)

namespace ClassicalOracleModel
sum left right => left.Query ⊕ right.Query

/-- Native coordinates retain the originating service. -/
@[expose, implicit_reducible]
public def Coordinate : ClassicalOracleModel → Type
  | .empty => Empty
  | .service signature => signature.Coordinate
  | .sum left right => left.Coordinate ⊕ right.Coordinate
ft right => left.HiddenState × right.HiddenState

public instance coordinateDecidableEq : (model : ClassicalOracleModel) →
    DecidableEq model.Coordinate
  | .empty => inferInstanceAs (DecidableEq Empty)
  | .service signature => signature.coordinateDecidableEq
  | .sum left right =>
      letI := coordinateDecidableEq left
      letI := coordinateDecidableEq right
      inferInstanceAs (DecidableEq (left.Coordinate ⊕ right.Coordinate))
HiddenState × right.HiddenState))
 | .sum _ right, .inr query => right.inputShape query
 | .sum _ right, .inr query => right.outputShape query
 | .sum _ right, .inr query => .inr (right.coordinate query)
right => left.Interpretation × right.Interpretation
ut).map
        (fun result => ((state.1, result.1), result.2))
 : Interpretation .empty := ()

      coordinate := coordinate }
etation where
  transition query _ input := (sample query input).map (fun result => ((), result))
_empty_classical_oracle_query (query : empty.Query) : False :=
  nomatch query

end ClassicalOracleModel

end QuantumAlg
