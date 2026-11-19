/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Model
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Model
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
Original file: QuantumAlg/Core/Base/Model.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Classical.Model
public import D5.S3.Quantum.FourierCircuit.Core.Base.Classical.Oracle
public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Model
public import D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Model

/-!
# Models of executable computation

Every execution selects its classical native operations and declared classical
oracle access. Quantum execution additionally selects native gates and quantum
oracle access. Pure quantum circuit accounting may use empty classical grants;
full algorithms choose their classical language explicitly in Components.
Mathematical quantum states and physical layouts still depend only on kind.
-/

namespace QuantumAlg

/-- The operation language shared by an implementation and its specification. -/
public inductive ExecutionModel where
  /-- Classical native operations and classical oracle access are independent selections. -/
  | classical (operations : ClassicalOpModel) (oracles : ClassicalOracleModel)
  /-- All four grants remain independent; empty classical grants suffice for pure unitary words. -/
  | quantum (gates : GateModel) (oracles : OracleModel)
      (operations : ClassicalOpModel := ClassicalOpModel.empty)
      (classicalOracles : ClassicalOracleModel := ClassicalOracleModel.empty)

namespace ExecutionModel


/-- The chosen classical native language is present in pure and hybrid execution. -/
@[expose, implicit_reducible]
public def classicalOperations : ExecutionModel → ClassicalOpModel
  | .classical operations _ => operations
  | .quantum _ _ operations _ => operations

/-- The classical oracle service declaration is independent of every other language. -/
@[expose, implicit_reducible]
public def classicalOracles : ExecutionModel → ClassicalOracleModel
  | .classical _ oracles => oracles
  | .quantum _ _ _ oracles => oracles


/-- Model-owned native coordinates for actual classical instructions. -/
@[expose, implicit_reducible]
public def ClassicalCoordinate (model : ExecutionModel) : Type :=
  model.classicalOperations.Coordinate

/-- Independently owned coordinates for actual classical oracle queries. -/
@[expose, implicit_reducible]
public def ClassicalOracleCoordinate (model : ExecutionModel) : Type :=
  model.classicalOracles.Coordinate


public instance classicalCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.ClassicalCoordinate := model.classicalOperations.coordinateDecidableEq

public instance classicalOracleCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.ClassicalOracleCoordinate := model.classicalOracles.coordinateDecidableEq


/-- Native gate coordinates are absent from classical execution. -/
@[expose, implicit_reducible]
public def GateCoordinate : ExecutionModel → Type
  | .classical _ _ => Empty
  | .quantum gates _ _ _ => gates.Coordinate

/-- Query coordinates are absent from classical execution and independent of native gates. -/
@[expose, implicit_reducible]
public def OracleCoordinate : ExecutionModel → Type
  | .classical _ _ => Empty
  | .quantum _ oracles _ _ => oracles.Coordinate

/-- Fixed preparation and measurement dimensions exist only in quantum execution. -/
@[expose, implicit_reducible]
public def SystemDimension : ExecutionModel → Type
  | .classical _ _ => Empty
  | .quantum _ _ _ _ => ℕ+

public instance gateCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.GateCoordinate := by
  cases model with
  | classical _ _ => exact inferInstanceAs (DecidableEq Empty)
  | quantum gates _ _ _ => exact gates.coordinateDecidableEq

public instance oracleCoordinateDecidableEq (model : ExecutionModel) :
    DecidableEq model.OracleCoordinate := by
  cases model with
  | classical _ _ => exact inferInstanceAs (DecidableEq Empty)
  | quantum _ oracles _ _ => exact oracles.coordinateDecidableEq

public instance systemDimensionDecidableEq (model : ExecutionModel) :
    DecidableEq model.SystemDimension := by
  cases model with
  | classical _ _ => exact inferInstanceAs (DecidableEq Empty)
  | quantum _ _ _ _ => exact inferInstanceAs (DecidableEq ℕ+)

end ExecutionModel

end QuantumAlg
