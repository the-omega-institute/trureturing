/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Native
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Realization/Native
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Realization/Native.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator

/-!
# Placing exact local token implementations at their original occurrences

A canonical local construction is moved to the argument positions of the
original application. The coordinate casts preserve all local basis values;
every complementary physical system retains its identity action.
-/

namespace QuantumAlg.UnitaryCircuit
noncomputable section

variable {sourceGates targetGates : GateModel} {oracles : OracleModel}
variable {count : Nat} {ambient : QuantumLayout count}

/-- Original placement certifies the dimensions required to relocate a local native word. -/
public lemma nativeDimensions (application : GateModel.Application sourceGates ambient) :
    ∀ index,
      (((sourceGates.signature application.occurrence.token).canonicalPlacement.layout).wire
        index).dimension = (ambient.wire (application.embedding.position index)).dimension := by
  intro index
  rw [application.embedding.wire_eq]
  exact (application.occurrence.placement.dimension_eq index).symm

/-- Canonical placement of the model operator agrees with the full original application. -/
public lemma nativeApplication_operatorAt
    (application : GateModel.Application sourceGates ambient) :
    operatorAt (sourceGates.signature application.occurrence.token).canonicalPlacement.layout
      ambient application.embedding.position (nativeDimensions application)
      (sourceGates.operator application.occurrence.token) = application.operator := by
  apply Subtype.ext
  ext row column
  rw [operatorAt_entry, GateModel.Application.application_operator_entry]
  have selected (basis : ambient.Basis) :
      selectedInput (sourceGates.signature application.occurrence.token).canonicalPlacement.layout
        ambient application.embedding.position (nativeDimensions application) basis =
      application.occurrence.placement.indexEquiv
        (application.embedding.splitBasis basis).1 := by
    funext index
    apply Fin.ext
    rfl
  rw [selected row, selected column]
  rfl


end
end QuantumAlg.UnitaryCircuit
