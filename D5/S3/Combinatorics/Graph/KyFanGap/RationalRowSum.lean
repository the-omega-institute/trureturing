/- GID: D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/RationalRowSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Basis.VectorSpace, mathlib/module/Mathlib.LinearAlgebra.Matrix.Symmetric, mathlib/module/Mathlib.NumberTheory.Real.Irrational]
   utility: none
   digest: Rationality of symmetric rational matrix constant weighted row sums and a nonsquare obstruction. -/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.NumberTheory.Real.Irrational
/-! Symmetry forces a constant normalized rational-matrix row sum to be rational. -/

noncomputable section
open Matrix
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum

/-- A nonzero constant weighted row sum of a symmetric rational matrix is rational. -/
theorem rational_row_sum {R : ℕ} (S : Matrix (Fin R) (Fin R) ℚ) (hS : S.IsSymm)
    (p : Fin R → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hrow : S.map ((↑) : ℚ → ℝ) *ᵥ p = c • (1 : Fin R → ℝ))
    (hp : ∑ i, p i = 1) : ∃ q : ℚ, c = (q : ℝ) := by
  let f : ℚ →ₗ[ℚ] ℝ := Algebra.linearMap ℚ ℝ
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℝ).injective)
  have hgrat (q : ℚ) : g (q : ℝ) = q := by
    have h := congrArg (fun l : ℚ →ₗ[ℚ] ℚ => l q) hg
    simpa [f] using h
  have hg1 : g 1 = 1 := by
    simpa only [Rat.cast_one] using hgrat 1
  have hgsmul (q : ℚ) (x : ℝ) : g ((q : ℝ) * x) = q * g x := by
    simpa [Rat.smul_def] using g.map_smul q x
  let w : Fin R → ℚ := fun i => g (p i / c)
  have hw (i : Fin R) : ∑ j, S i j * w j = 1 := by
    have hr := congrFun hrow i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_one] at hr
    have hr' : ∑ j, (S i j : ℝ) * (p j / c) = 1 := by
      simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [← Finset.sum_mul, hr, mul_inv_cancel₀ hc]
    have hr'' := congrArg g hr'
    rw [map_sum] at hr''
    simpa only [w, hgsmul, hg1] using hr''
  have hSr : (S.map ((↑) : ℚ → ℝ)).IsSymm := hS.map _
  have hwr : S.map ((↑) : ℚ → ℝ) *ᵥ (fun i => (w i : ℝ)) = 1 := by
    ext i
    simpa only [mulVec, dotProduct, Matrix.map_apply, Pi.one_apply,
      ← Rat.cast_mul, ← Rat.cast_sum, Rat.cast_one] using congrArg ((↑) : ℚ → ℝ) (hw i)
  have hid := hSr.dotProduct_mulVec_comm (x := p) (y := fun i => (w i : ℝ))
  rw [hwr, hrow] at hid
  have hcw : c * ∑ i, (w i : ℝ) = 1 := by
    simpa [dotProduct, Finset.mul_sum, mul_comm, hp] using hid.symm
  have hsum : (∑ i, (w i : ℝ)) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcw
    exact zero_ne_one hcw
  refine ⟨(∑ i, w i)⁻¹, ?_⟩
  push_cast
  simpa only [one_div] using (eq_div_iff hsum).mpr hcw

/-- A symmetric rational matrix cannot have normalized weighted row sum equal to
an inverse square root of a nonsquare natural number. -/
theorem nonsquare_row_sum_ne {R : ℕ} (S : Matrix (Fin R) (Fin R) ℚ)
    (hS : S.IsSymm) {k : ℕ} (hk : ¬ IsSquare k)
    (p : Fin R → ℝ) (hp : ∑ i, p i = 1) :
    S.map ((↑) : ℚ → ℝ) *ᵥ p ≠ (1 / Real.sqrt k) • (1 : Fin R → ℝ) := by
  intro hrow
  have hirr : Irrational (1 / Real.sqrt k) := by
    simpa only [one_div] using (irrational_sqrt_natCast_iff.mpr hk).inv
  obtain ⟨q, hq⟩ := rational_row_sum S hS p (1 / Real.sqrt k) hirr.ne_zero hrow hp
  exact hirr ⟨q, hq.symm⟩

end D5.S3.Combinatorics.Graph.KyFanGap.RationalRowSum
