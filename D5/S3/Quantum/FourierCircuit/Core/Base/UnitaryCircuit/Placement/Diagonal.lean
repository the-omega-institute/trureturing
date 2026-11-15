/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Diagonal
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Placement/Diagonal
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
Original file: QuantumAlg/Core/Base/UnitaryCircuit/Placement/Diagonal.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement
public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Diagonal
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Diagonal
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding

/-!
# Diagonal targets at explicitly selected physical positions

The phase reads the selected ambient values in their supplied order. Every
other system remains unchanged. This follows from complete physical placement
and does not introduce an executable gate with a separately supplied cost.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {small large : Nat} (source : QuantumLayout small) (target : QuantumLayout large)
variable (position : Fin small ↪ Fin large)
variable (dimensions : ∀ index,
  (source.wire index).dimension = (target.wire (position index)).dimension)

/-- A placed diagonal target reads exactly the selected ambient coordinates. -/
public lemma operatorAt_diagonal (operator : UnitaryOperator source.register)
    (weight : source.Basis → Complex)
    (diagonal : (operator : HilbertOperator source.register) = Matrix.diagonal weight) :
    (operatorAt source target position dimensions operator : HilbertOperator target.register) =
      Matrix.diagonal (fun basis => weight (selectedInput source target position dimensions basis))
        := by
  have actual := QuantumLayout.Embedding.embedding_liftOperator_diagonal
    (relocatedPlacement source target position dimensions) operator weight diagonal
  refine actual.trans ?_
  apply congrArg Matrix.diagonal
  funext basis
  apply congrArg weight
  funext index
  apply Fin.ext
  rfl

end

end QuantumAlg.UnitaryCircuit
