/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Placement
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Oracle/Placement
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
Original file: QuantumAlg/Core/Base/Oracle/Placement.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Oracle.Model
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Selection
import all D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator
public import D5.S3.Quantum.FourierCircuit.Core.Base.Tensor.Certified
import all D5.S3.Quantum.FourierCircuit.Core.Base.Tensor.Certified

/-!
# Applying declared queries to actual ambient wires

An application embeds the occurrence's own physical wires in the ambient
layout. Its operator acts on those ordered wires and tensors with identity on
their full complement. The embedding does not supply an arbitrary basis change.
-/

namespace QuantumAlg.OracleModel

/-- A granted query occurrence on exactly the selected physical wires of an ambient layout. -/
public structure Application (model : OracleModel) {count : Nat}
    (layout : QuantumLayout count) where
  /-- The actual token and its dimension-correct physical placement. -/
  occurrence : Occurrence model
  /-- These same physical wires occur at the selected ambient positions. -/
  embedding : QuantumLayout.Embedding occurrence.placement.layout layout

namespace Application

variable {model : OracleModel} {count : Nat} {layout : QuantumLayout count}

/-- The query event coordinate remains fixed by the original query instance. -/
@[expose]
public def coordinate (application : Application model layout) : model.Coordinate :=
  application.occurrence.coordinate

/-- Act on the selected systems and preserve the complete complementary subsystem. -/
@[expose]
public noncomputable def operator (application : Application model layout)
    (environment : Interpretation model) :
    UnitaryOperator layout.register :=
  UnitaryOperator.reindex application.embedding.splitBasis.symm
    (UnitaryOperator.prodTensor (application.occurrence.operator environment)
      (1 : UnitaryOperator (layout.complementRegister application.embedding.selection)))

/-- Query accounting cannot be detached from the applied query instance. -/
public lemma oracle_application_coordinate (application : Application model layout) :
    application.coordinate = model.coordinate application.occurrence.query := rfl

/-- Application retains the original physical identity at every gate argument. -/
public lemma oracle_application_wire_identity (application : Application model layout)
    (index : Fin (model.signature application.occurrence.query).systemCount) :
    (layout.wire (application.embedding.position index)).identity =
      (application.occurrence.placement.layout.wire index).identity :=
  congrArg QuantumWire.identity (application.embedding.wire_eq index)

/-- Each matrix entry factors through the actual query and identity on its full complement. -/
public lemma oracle_application_operator_entry (application : Application model layout)
    (environment : Interpretation model)
    (row column : layout.Basis) :
    application.operator environment row column =
      (application.occurrence.operator environment)
        (application.embedding.splitBasis row).1
        (application.embedding.splitBasis column).1 *
      (if (application.embedding.splitBasis row).2 =
          (application.embedding.splitBasis column).2 then 1 else 0) := by
  change UnitaryOperator.prodTensor (application.occurrence.operator environment)
    (1 : UnitaryOperator (layout.complementRegister application.embedding.selection))
    (application.embedding.splitBasis row) (application.embedding.splitBasis column) = _
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

end Application

end QuantumAlg.OracleModel
