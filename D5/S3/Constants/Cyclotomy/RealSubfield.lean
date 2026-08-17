/- GID: D5/S3/Constants/Cyclotomy/RealSubfield
   generality: I
   mirror-B: D5/B/S3/Constants/Cyclotomy/RealSubfield
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The real fifth-cyclotomic generator adjoins exactly root five. -/

import D5.S3.Constants.PentagonCosines
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/- Provenance: Native proof over pinned mathlib and an existing D5 pentagon identity. -/

open scoped IntermediateField

namespace D5.S3.Constants.Cyclotomy.RealSubfield

/-- The real generator `2 cos (2π/5)` of the fifth cyclotomic field adjoins
the same subfield of `ℝ` over `ℚ` as `√5`. -/
theorem real_cyclotomic_generator_adjoin_eq_sqrt_five :
    ℚ⟮2 * Real.cos (2 * Real.pi / 5)⟯ = ℚ⟮Real.sqrt 5⟯ := by
  have hgen :
      2 * Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 2 := by
    rw [PentagonCosines.pentagon_golden_cosines.2.1, Real.inv_goldenRatio]
    ring
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, hgen]
    exact (ℚ⟮Real.sqrt 5⟯).div_mem
      ((ℚ⟮Real.sqrt 5⟯).sub_mem
        (IntermediateField.subset_adjoin ℚ {Real.sqrt 5} (by simp)) (by norm_num))
      (by norm_num)
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    have hmem :
        2 * Real.cos (2 * Real.pi / 5) ∈
          ℚ⟮2 * Real.cos (2 * Real.pi / 5)⟯ :=
      IntermediateField.subset_adjoin ℚ {2 * Real.cos (2 * Real.pi / 5)} (by simp)
    have hsqrt :
        Real.sqrt 5 = 2 * (2 * Real.cos (2 * Real.pi / 5)) + 1 := by
      rw [hgen]
      ring
    rw [hsqrt]
    exact (ℚ⟮2 * Real.cos (2 * Real.pi / 5)⟯).add_mem
      ((ℚ⟮2 * Real.cos (2 * Real.pi / 5)⟯).mul_mem (by norm_num) hmem)
      (by norm_num)

end D5.S3.Constants.Cyclotomy.RealSubfield
