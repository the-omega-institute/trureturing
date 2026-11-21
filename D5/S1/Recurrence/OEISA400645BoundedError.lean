import D5.S1.Recurrence.OEISA400645
import D5.S1.Recurrence.Asymptotic.DominantRootForcing

set_option autoImplicit false

noncomputable section

namespace D5.S1.Recurrence.OEISA400645BoundedError

open Polynomial Asymptotics Filter
open D5.S1.Recurrence.OEISA400645
open D5.S0.Tower.NonPisotFrontier.BetaThirteen

/-- The characteristic polynomial `y^4 - y^3 - y^2 - y + 1` of the squared recurrence. -/
private def charPoly : ℝ[X] := X ^ 4 - X ^ 3 - X ^ 2 - X + 1

private theorem charPoly_natDegree : charPoly.natDegree = 4 := by
  unfold charPoly
  compute_degree!

private theorem charPoly_sum (u : ℕ → ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range (charPoly.natDegree + 1), charPoly.coeff k * u (j + k) =
      u j - u (j + 1) - u (j + 2) - u (j + 3) + u (j + 4) := by
  rw [charPoly_natDegree]
  simp [Finset.sum_range_succ, charPoly, coeff_X_pow, coeff_X, coeff_one]
  ring

private theorem charPoly_eval (y : ℝ) : charPoly.eval y = y ^ 4 - y ^ 3 - y ^ 2 - y + 1 := by
  simp [charPoly]

private theorem rootMultiplicity_charPoly : charPoly.rootMultiplicity squaredLimit = 1 := by
  have hr := r_bounds
  have hP0 : charPoly ≠ 0 := fun h => by
    have := charPoly_eval 0
    rw [h, eval_zero] at this
    norm_num at this
  have hroot : charPoly.IsRoot squaredLimit := by
    rw [IsRoot, charPoly_eval]
    exact r_poly
  have hpos : 0 < charPoly.rootMultiplicity squaredLimit :=
    (rootMultiplicity_pos hP0).mpr hroot
  have hnot : ¬ 1 < charPoly.rootMultiplicity squaredLimit := by
    rw [one_lt_rootMultiplicity_iff_isRoot hP0]
    rintro ⟨-, hd⟩
    rw [IsRoot] at hd
    simp [charPoly] at hd
    nlinarith [hr.1]
  omega

/-- Every complex root of `charPoly` other than `squaredLimit` has modulus below its square
root: the polynomial is `(y² - β y + 1)(y² - (1 - β) y + 1)` with `β = (1 + √13)/2`. -/
private theorem other_roots (z : ℂ) (hz : (charPoly.map (algebraMap ℝ ℂ)).IsRoot z)
    (hne : z ≠ (squaredLimit : ℂ)) : ‖z‖ < Real.sqrt squaredLimit := by
  have hr := r_bounds
  have hq := r_quad
  have hβ := betaThirteen_quadratic
  have hβ2 := two_lt_betaThirteen
  have hβ3 : betaThirteen < 5 / 2 := by
    have := sqrt_thirteen_bounds.2
    simp only [betaThirteen]
    linarith
  have hz' : z ^ 4 - z ^ 3 - z ^ 2 - z + 1 = 0 := by
    simpa [IsRoot, charPoly] using hz
  have hfac : (z ^ 2 - (betaThirteen : ℂ) * z + 1) * (z ^ 2 - (1 - (betaThirteen : ℂ)) * z + 1)
      = 0 := by
    have hβC : (betaThirteen : ℂ) ^ 2 = betaThirteen + 3 := by exact_mod_cast hβ
    linear_combination hz' - z ^ 2 * hβC
  have hsq : Complex.normSq z < squaredLimit := by
    rcases mul_eq_zero.mp hfac with h1 | h2
    · -- the real pair `squaredLimit`, `β - squaredLimit`
      have hqC : (squaredLimit : ℂ) ^ 2 - (betaThirteen : ℂ) * squaredLimit + 1 = 0 := by
        exact_mod_cast hq
      have hprod : (z - squaredLimit) * (z - (betaThirteen - squaredLimit)) = 0 := by
        linear_combination h1 - hqC
      have hz2 : z = ((betaThirteen - squaredLimit : ℝ) : ℂ) := by
        have := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
        rw [sub_eq_zero] at this
        rw [this]
        push_cast
        ring
      rw [hz2, Complex.normSq_ofReal]
      nlinarith
    · -- the unit-circle pair
      set t : ℝ := 1 - betaThirteen with ht
      have htC : (1 - (betaThirteen : ℂ)) = (t : ℂ) := by rw [ht]; push_cast; ring
      rw [htC] at h2
      have hre := congrArg Complex.re h2
      have him := congrArg Complex.im h2
      simp [sq, Complex.mul_re, Complex.mul_im] at hre him
      have hy : z.im ≠ 0 := by
        intro h0
        rw [h0] at hre
        nlinarith [sq_nonneg (z.re - t / 2)]
      have hx : z.re = t / 2 := by
        have : z.im * (2 * z.re - t) = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_left hy
        linarith
      rw [Complex.normSq_apply]
      rw [hx] at hre
      nlinarith
  rw [Complex.norm_def]
  exact Real.sqrt_lt_sqrt (Complex.normSq_nonneg z) hsq

end D5.S1.Recurrence.OEISA400645BoundedError
