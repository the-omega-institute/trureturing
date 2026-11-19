/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Diagonal
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding/Diagonal
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
Original file: QuantumAlg/Core/Base/Layout/Quantum/Embedding/Diagonal.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Embedding

/-!
# Diagonal operators on embedded physical subsystems

Identity extension retains the selected diagonal phase and leaves every
complementary coordinate unchanged. This is an operator equality, without a
basis-state or initialized-spectator assumption.
-/

namespace QuantumAlg.QuantumLayout.Embedding

noncomputable section

variable {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}

/-- A diagonal operator stays diagonal under physical embedding, with its exact selected phase. -/
public lemma embedding_liftOperator_diagonal (placement : Embedding source target)
    (operator : UnitaryOperator source.register) (weight : source.Basis → Complex)
    (diagonal : (operator : HilbertOperator source.register) = Matrix.diagonal weight) :
    (placement.liftOperator operator : HilbertOperator target.register) =
      Matrix.diagonal (fun basis => weight (placement.splitBasis basis).1) := by
  ext row column
  rw [liftOperator_entry, diagonal]
  by_cases same : row = column
  · subst column
    simp
  · by_cases selected : (placement.splitBasis row).1 = (placement.splitBasis column).1
    · have complement : (placement.splitBasis row).2 ≠ (placement.splitBasis column).2 :=
        fun equal => same (placement.splitBasis.injective (Prod.ext selected equal))
      simp [same, selected, complement]
    · simp [same, selected]

end

end QuantumAlg.QuantumLayout.Embedding
