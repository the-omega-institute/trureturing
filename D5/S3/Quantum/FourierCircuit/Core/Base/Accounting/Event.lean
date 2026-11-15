/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/Event
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Accounting/Event
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
Original file: QuantumAlg/Core/Base/Accounting/Event.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Model

/-!
# Model-relative execution events

A native gate coordinate belongs to the selected gate model. A query coordinate
belongs to the independently granted oracle model. Zero preparation and Z
measurement retain their fixed semantics and actual positive system dimension.
No inverse or control operation on an event creates a new executable capability.
-/

namespace QuantumAlg.Resource

/-- Event coordinates of one declared execution language. -/
public inductive Event (model : ExecutionModel) where
  /-- One actual operation from the selected classical native declaration. -/
  | classicalOperation (coordinate : model.ClassicalCoordinate)
  /-- One query granted by the selected classical oracle declaration. -/
  | classicalQuery (coordinate : model.ClassicalOracleCoordinate)
  /-- One native instance emits its model-owned gate coordinate. -/
  | gate (coordinate : model.GateCoordinate)
  /-- One granted query emits its declaration-owned query coordinate. -/
  | oracle (coordinate : model.OracleCoordinate)
  /-- Prepare one fresh physical system in its zero computational-basis state. -/
  | preparation (dimension : model.SystemDimension)
  /-- Measure one actual physical system in its computational Z basis. -/
  | measurement (dimension : model.SystemDimension)
deriving DecidableEq

namespace Event


end Event

end QuantumAlg.Resource
