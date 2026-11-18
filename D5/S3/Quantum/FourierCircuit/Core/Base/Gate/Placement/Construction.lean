/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Construction
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Construction
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
Original file: QuantumAlg/Core/Base/Gate/Placement/Construction.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement

/-!
# Applying a declared gate instance at actual wire positions

A finite injection selects distinct ambient wires in argument order. Each
selected wire must have the declared dimension. The local layout and its
embedding are derived from these same positions, with no independent operator
or physical-identity claim.
-/

namespace QuantumAlg.GateModel.Application

/-- Construct the actual local layout and embedding from dimension-correct ambient positions. -/
@[expose]
public def ofPositions (model : GateModel) (token : model.Token)
    {count : Nat} (layout : QuantumLayout count)
    (position : Fin (model.signature token).systemCount ↪ Fin count)
    (dimensions : ∀ index,
      (layout.wire (position index)).dimension = (model.signature token).dimension index) :
    Application model layout where
  occurrence :=
    { token := token
      placement :=
        { layout :=
            { wire := fun index => layout.wire (position index)
              identityInjective := fun _ _ same =>
                position.injective (layout.identityInjective same) }
          dimension_eq := dimensions } }
  embedding := { position := position, wire_eq := fun _ => rfl }


end QuantumAlg.GateModel.Application
