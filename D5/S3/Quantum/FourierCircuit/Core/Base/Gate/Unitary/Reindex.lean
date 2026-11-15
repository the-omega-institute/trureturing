/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Gate/Unitary/Reindex
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
Original file: QuantumAlg/Core/Base/Gate/Unitary/Reindex.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Control.Operator
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary

/-!
# Exact operator transport between basis conventions

Changing basis labels preserves identity, composition and the original
operator after inverse transport. These are mathematical identities and
introduce no executable gate or access capability.
-/

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S T : Register}

/-- Relabelling the identity gives the identity on the target register. -/
public lemma unitaryOperator_reindex_one (equivalence : R.Index ≃ S.Index) :
    reindex equivalence (1 : UnitaryOperator R) = (1 : UnitaryOperator S) := by
  apply Subtype.ext
  exact Matrix.submatrix_one_equiv equivalence.symm

/-- Exact operator composition commutes with a common change of basis labels. -/
public lemma unitaryOperator_reindex_mul (equivalence : R.Index ≃ S.Index)
    (first second : UnitaryOperator R) :
    reindex equivalence (first * second) =
      reindex equivalence first * reindex equivalence second := by
  apply Subtype.ext
  exact (Matrix.submatrix_mul_equiv (first : HilbertOperator R) (second : HilbertOperator R)
    equivalence.symm equivalence.symm equivalence.symm).symm


/-- Transporting back to the original basis restores the complete operator. -/
public lemma unitaryOperator_reindex_cancel (equivalence : R.Index ≃ S.Index)
    (operator : UnitaryOperator R) :
    reindex equivalence.symm (reindex equivalence operator) = operator := by
  apply Subtype.ext
  ext row column
  change operator (equivalence.symm (equivalence row))
    (equivalence.symm (equivalence column)) = operator row column
  rw [equivalence.symm_apply_apply, equivalence.symm_apply_apply]

end

end QuantumAlg.UnitaryOperator

namespace QuantumAlg.HilbertVector

noncomputable section

variable {R S T : Register}


end


end QuantumAlg.HilbertVector

namespace QuantumAlg.NormalizedVector

noncomputable section

variable {R S : Register}


end

end QuantumAlg.NormalizedVector

namespace QuantumAlg.UnitaryOperator

noncomputable section

variable {R S : Register}


end


end QuantumAlg.UnitaryOperator
