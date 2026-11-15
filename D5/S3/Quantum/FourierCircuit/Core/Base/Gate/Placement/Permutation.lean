/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/Placement/Permutation
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
Original file: QuantumAlg/Core/Base/Gate/Placement/Permutation.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Placement
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Model
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Signature
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding

/-!
# Selected and complementary coordinates of a placed native gate

The basis equivalence reads the model’s ordered arguments and preserves the
complete unselected register.
-/

namespace QuantumAlg.GateModel.Application

noncomputable section

variable {model : GateModel} {count : Nat} {layout : QuantumLayout count}

/-- Read the model's ordered argument values and the full untouched complement. -/
@[expose]
public def basisEquiv (application : Application model layout) :
    layout.Basis ≃ (model.signature application.occurrence.token).Basis ×
      layout.ComplementBasis application.embedding.selection :=
  application.embedding.splitBasis.trans
    (Equiv.prodCongr application.occurrence.placement.indexEquiv (Equiv.refl _))

end

end QuantumAlg.GateModel.Application
