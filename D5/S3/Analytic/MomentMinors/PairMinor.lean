/- GID: D5/S3/Analytic/MomentMinors/PairMinor
   generality: G
   mirror-B: D5/B/S3/Analytic/MomentMinors/PairMinor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Positive semidefiniteness of second minors along arbitrary finite index pairs. -/

import Mathlib.Analysis.Matrix.Order

/-! Second minors as a nonnegative congruence of a tensor square. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Matrix
open scoped Kronecker

namespace D5.S3.Analytic.MomentMinors.PairMinor

/-- Second minors of a positive semidefinite real matrix form a positive
semidefinite matrix, with repeated and overlapping index pairs allowed. -/
theorem pairMinor_posSemidef {ι κ : Type*} [Fintype ι] [Finite κ]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (p q : κ → ι) :
    Matrix.PosSemidef (fun a b => A (p a) (p b) * A (q a) (q b) -
      A (p a) (q b) * A (q a) (p b) : Matrix κ κ ℝ) := by
  classical
  let T : Matrix (ι × ι) κ ℝ := fun i a =>
    (if i = (p a, q a) then 1 else 0) - (if i = (q a, p a) then 1 else 0)
  have h := ((hA.kronecker hA).conjTranspose_mul_mul_same T).smul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have he : (fun a b => A (p a) (p b) * A (q a) (q b) -
      A (p a) (q b) * A (q a) (p b) : Matrix κ κ ℝ) =
      (1 / 2 : ℝ) • (Tᴴ * (A ⊗ₖ A) * T) := by
    funext a b
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply, T, star_trivial,
      sub_mul, mul_sub, Finset.sum_sub_distrib]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul, mul_one]
    simp only [Matrix.kroneckerMap_apply]
    ring
  rw [he]
  exact h

end D5.S3.Analytic.MomentMinors.PairMinor
