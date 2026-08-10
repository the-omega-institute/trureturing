/- GID: D5/S1/Depth/GoldenHurwitzBound
   generality: I
   mirror-B: D5/B/S1/Depth/GoldenHurwitzBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No rational lies within one over root-five den squared plus den of the golden ratio. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination

/- Provenance: Native proof over pinned mathlib. -/

namespace D5.S1.Depth

private theorem two_lt_sqrt_five : 2 < Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 5]

/-- The golden quadratic form vanishes at no rational: `num^2 - num*den - den^2 ≠ 0`. -/
private theorem golden_form_ne_zero (q : ℚ) :
    q.num ^ 2 - q.num * (q.den : ℤ) - (q.den : ℤ) ^ 2 ≠ 0 := by
  intro h
  have hdne : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hsum : Real.goldenRatio + Real.goldenConj = 1 := Real.goldenRatio_add_goldenConj
  have hprod : Real.goldenRatio * Real.goldenConj = -1 := Real.goldenRatio_mul_goldenConj
  have hr : (q.num : ℝ) ^ 2 - q.num * q.den - (q.den : ℝ) ^ 2 = 0 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  have hzero : ((q.num : ℝ) - q.den * Real.goldenRatio) *
      ((q.num : ℝ) - q.den * Real.goldenConj) = 0 := by
    linear_combination hr - (q.num : ℝ) * q.den * hsum + (q.den : ℝ) ^ 2 * hprod
  rcases mul_eq_zero.mp hzero with hcase | hcase
  · refine Real.goldenRatio_irrational ⟨q, ?_⟩
    rw [Rat.cast_def, div_eq_iff hdne]
    linarith
  · refine Real.goldenConj_irrational ⟨q, ?_⟩
    rw [Rat.cast_def, div_eq_iff hdne]
    linarith

/--
Effective Hurwitz bound at the golden ratio: every rational `q` keeps distance
strictly greater than `1 / (sqrt 5 * den q ^ 2 + den q)` from `phi`.  This is
the uniform badly-approximable form of the sharp constant `sqrt 5`: along the
Fibonacci convergents the scaled error approaches `1 / (sqrt 5 * den ^ 2)`, so
the constant `sqrt 5` cannot be enlarged.
-/
theorem golden_hurwitz_bound (q : ℚ) :
    1 / (Real.sqrt 5 * (q.den : ℝ) ^ 2 + q.den) < |Real.goldenRatio - q| := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 : (2 : ℝ) < Real.sqrt 5 := two_lt_sqrt_five
  have hd0 : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast (q.pos : 1 ≤ q.den)
  have hdne : (q.den : ℝ) ≠ 0 := hd0.ne'
  have hsum : Real.goldenRatio + Real.goldenConj = 1 := Real.goldenRatio_add_goldenConj
  have hprod : Real.goldenRatio * Real.goldenConj = -1 := Real.goldenRatio_mul_goldenConj
  -- The integer certificate: the golden form is at least one in absolute value.
  have hone : (1 : ℝ) ≤ |(q.num : ℝ) ^ 2 - q.num * q.den - (q.den : ℝ) ^ 2| := by
    exact_mod_cast Int.one_le_abs (golden_form_ne_zero q)
  have hp : (q.num : ℝ) = q * q.den := by
    rw [Rat.cast_def]; field_simp
  -- Factor the golden form through both roots of `x^2 - x - 1`.
  have hfactor : (q.num : ℝ) ^ 2 - q.num * q.den - (q.den : ℝ) ^ 2 =
      ((q.den : ℝ) * ((q : ℝ) - Real.goldenRatio)) *
        ((q.den : ℝ) * ((q : ℝ) - Real.goldenConj)) := by
    rw [hp]
    linear_combination ((q.den : ℝ) ^ 2 * (q : ℝ)) * hsum - (q.den : ℝ) ^ 2 * hprod
  set δ : ℝ := |Real.goldenRatio - (q : ℝ)| with hδ_def
  have hδ0 : (0 : ℝ) ≤ δ := abs_nonneg _
  have hδq : |(q : ℝ) - Real.goldenRatio| = δ := by rw [hδ_def, abs_sub_comm]
  -- Triangle inequality: the conjugate root is at most `sqrt 5` farther away.
  have htri : |(q : ℝ) - Real.goldenConj| ≤ δ + Real.sqrt 5 := by
    calc |(q : ℝ) - Real.goldenConj|
        ≤ |(q : ℝ) - Real.goldenRatio| + |Real.goldenRatio - Real.goldenConj| :=
          abs_sub_le _ _ _
      _ = δ + Real.sqrt 5 := by
          rw [hδq, Real.goldenRatio_sub_goldenConj, abs_of_nonneg hs0]
  -- Key inequality: `1 ≤ den^2 * δ * (δ + sqrt 5)`.
  have hkey : (1 : ℝ) ≤ (q.den : ℝ) ^ 2 * δ * (δ + Real.sqrt 5) := by
    have habs : |(q.num : ℝ) ^ 2 - q.num * q.den - (q.den : ℝ) ^ 2| =
        ((q.den : ℝ) * δ) * ((q.den : ℝ) * |(q : ℝ) - Real.goldenConj|) := by
      rw [hfactor, abs_mul, abs_mul, abs_mul, abs_of_pos hd0, hδq]
    calc (1 : ℝ) ≤ |(q.num : ℝ) ^ 2 - q.num * q.den - (q.den : ℝ) ^ 2| := hone
      _ = ((q.den : ℝ) * δ) * ((q.den : ℝ) * |(q : ℝ) - Real.goldenConj|) := habs
      _ ≤ ((q.den : ℝ) * δ) * ((q.den : ℝ) * (δ + Real.sqrt 5)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htri hd0.le)
            (mul_nonneg hd0.le hδ0)
      _ = (q.den : ℝ) ^ 2 * δ * (δ + Real.sqrt 5) := by ring
  -- Conclude by excluding `δ ≤ 1 / (sqrt 5 * den^2 + den)`.
  rw [← not_le]
  intro hc
  have hA : (0 : ℝ) < Real.sqrt 5 * (q.den : ℝ) ^ 2 + q.den := by positivity
  have hAd : δ * (Real.sqrt 5 * (q.den : ℝ) ^ 2 + q.den) ≤ 1 := (le_div_iff₀ hA).mp hc
  set t : ℝ := (q.den : ℝ) * δ with ht_def
  have ht0 : (0 : ℝ) ≤ t := mul_nonneg hd0.le hδ0
  have hii : t * (Real.sqrt 5 * q.den + 1) ≤ 1 := by
    calc t * (Real.sqrt 5 * q.den + 1)
        = δ * (Real.sqrt 5 * (q.den : ℝ) ^ 2 + q.den) := by rw [ht_def]; ring
      _ ≤ 1 := hAd
  have hi : (1 : ℝ) ≤ t ^ 2 + Real.sqrt 5 * q.den * t := by
    calc (1 : ℝ) ≤ (q.den : ℝ) ^ 2 * δ * (δ + Real.sqrt 5) := hkey
      _ = t ^ 2 + Real.sqrt 5 * q.den * t := by rw [ht_def]; ring
  have htsq : t ≤ t ^ 2 := by nlinarith
  have hu2 : (2 : ℝ) ≤ Real.sqrt 5 * q.den := by
    nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ (q.den : ℝ) - 1)]
  have ht13 : 3 * t ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left
      (by linarith : (3 : ℝ) ≤ Real.sqrt 5 * q.den + 1) ht0]
  have ht00 : t = 0 := by
    nlinarith [mul_le_mul_of_nonneg_left ht13 ht0]
  rw [ht00] at hi
  norm_num at hi

end D5.S1.Depth
