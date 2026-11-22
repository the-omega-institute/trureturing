/- GID: D5/S3/Quantum/TwoSource/MasslessResidue
   generality: G
   mirror-B: D5/B/S3/Quantum/TwoSource/MasslessResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: Positive complementary residues have a sharp, rigid mixed entry bound. -/

module

public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A real symmetric residue and its positive complement describe two normalized sources. -/

@[expose] public section
namespace D5.S3.Quantum.TwoSource.MasslessResidue

open Matrix

/-- The realization with identical diagonal weights for the two sources. -/
noncomputable def balanced (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, r; r, 1/2]

private theorem balanced_pos {r : ℝ} (hr : |r| ≤ 1/2) : (balanced r).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [balanced]
  · intro x
    obtain ⟨hl,hu⟩ := abs_le.mp hr
    have hplus : 0 ≤ (1/2+r)*((x 0 + x 1)^2) := mul_nonneg (by linarith) (sq_nonneg _)
    have hminus : 0 ≤ (1/2-r)*((x 0 - x 1)^2) := mul_nonneg (by linarith) (sq_nonneg _)
    simp [dotProduct, mulVec, balanced, Fin.sum_univ_two, Pi.star_apply]
    linarith only [hplus, hminus]

private theorem complement_balanced (r : ℝ) : 1 - balanced r = balanced (-r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [balanced, Matrix.one_apply]

private theorem trace_tests {Z : Matrix (Fin 2) (Fin 2) ℝ}
    (hz : Z.PosSemidef) (hc : (1-Z).PosSemidef) :
    (2 * |Z 0 1| ≤ Z 0 0 + Z 1 1) ∧ (Z 0 0 + Z 1 1 ≤ 2 - 2 * |Z 0 1|) := by
  have hsym : Z 1 0 = Z 0 1 := by simpa using hz.isHermitian.apply 0 1
  have a := hz.dotProduct_mulVec_nonneg ![1, (1 : ℝ)]
  have b := hz.dotProduct_mulVec_nonneg ![1, (-1 : ℝ)]
  have c := hc.dotProduct_mulVec_nonneg ![1, (1 : ℝ)]
  have d := hc.dotProduct_mulVec_nonneg ![1, (-1 : ℝ)]
  norm_num [dotProduct, mulVec, Fin.sum_univ_two, Matrix.one_apply, hsym] at a b c d
  rcases le_or_gt 0 (Z 0 1) with h | h
  · rw [abs_of_nonneg h]; constructor <;> linarith
  · rw [abs_of_neg h]; constructor <;> linarith

/-- The mixed entry fills exactly the closed half interval. At either endpoint every
admissible residue has equal diagonal weights and is uniquely determined by its mixed entry. -/
theorem sharp_mixed_residue (r : ℝ) :
    ((∃ Z : Matrix (Fin 2) (Fin 2) ℝ, Z.PosSemidef ∧ (1-Z).PosSemidef ∧ Z 0 1 = r) ↔
      |r| ≤ 1/2) ∧
    (|r| = 1/2 → ∀ Z : Matrix (Fin 2) (Fin 2) ℝ,
      Z.PosSemidef → (1-Z).PosSemidef → Z 0 1 = r → Z = balanced r) := by
  constructor
  · constructor
    · rintro ⟨Z,hz,hc,rfl⟩
      obtain ⟨hl,hu⟩ := trace_tests hz hc
      linarith
    · intro hr
      refine ⟨balanced r, balanced_pos hr, ?_, by simp [balanced]⟩
      rw [complement_balanced]; exact balanced_pos (by simpa using hr)
  · intro hr Z hz hc hm
    have hsym : Z 1 0 = r := by simpa [hm] using hz.isHermitian.apply 0 1
    obtain ⟨hl,hu⟩ := trace_tests hz hc
    rw [hm,hr] at hl hu
    have trace : Z 0 0 + Z 1 1 = 1 := by linarith
    have det := hz.det_nonneg
    rw [Matrix.det_fin_two, hm, hsym] at det
    have hr2 : r*r = 1/4 := by
      rcases le_or_gt 0 r with h | h
      · rw [abs_of_nonneg h] at hr; rw [hr]; norm_num
      · rw [abs_of_neg h] at hr
        have e : r = -(1/2) := by linarith
        rw [e]
        norm_num
    rw [hr2] at det
    have h11 : Z 1 1 = 1 - Z 0 0 := by linarith
    rw [h11] at det
    have h00 : Z 0 0 = 1/2 := by nlinarith [sq_nonneg (Z 0 0 - 1/2)]
    have hd : Z 1 1 = 1/2 := by linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [balanced, h00, hd, hm, hsym]

end D5.S3.Quantum.TwoSource.MasslessResidue
