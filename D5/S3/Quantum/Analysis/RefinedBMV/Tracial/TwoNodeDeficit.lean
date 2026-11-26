/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TwoNodeDeficit
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree comparison for the centered homogeneous polynomial at reciprocal nodes. -/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The two-node deficit at reciprocal positive nodes controls every lower
degree after multiplying by the appropriate cubic and exponential factors. -/

namespace RefinedBMV.Tracial

open Real

noncomputable section

/-- The complete homogeneous polynomial at `exp x` and `exp (-x)`
minus its value at the reciprocal geometric center. -/
def twoNodeDeficit (n : ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), exp x ^ k * exp (-x) ^ (n - k)) - ((n : ℝ) + 1)

private theorem twoNodeDeficit_at_zero (n : ℕ) : twoNodeDeficit n 0 = 0 := by
  simp [twoNodeDeficit]

private def degreePrimitive (n : ℕ) (t : ℝ) : ℝ :=
  sinh (((n : ℝ) + 1) * t) / ((n : ℝ) + 1) - sinh t

private theorem twoNodeDeficit_eq_primitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    twoNodeDeficit n x = (((n : ℝ) + 1) / sinh x) * degreePrimitive n x := by
  have h := geom_sum₂_mul (exp x) (exp (-x)) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  have hsum : (∑ k ∈ Finset.range (n + 1), exp x ^ k * exp (-x) ^ (n - k)) =
      sinh (((n : ℝ) + 1) * x) / sinh x := by
    apply (eq_div_iff (sinh_pos_iff.mpr hx).ne').mpr
    simp only [sinh_eq, ← exp_nat_mul, Nat.cast_add, Nat.cast_one, mul_neg] at h ⊢
    linarith only [h]
  rw [twoNodeDeficit, hsum, degreePrimitive]
  field_simp [(sinh_pos_iff.mpr hx).ne']

private theorem scaled_sinh_lower {a b t : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    a / b * exp (-(b - a) * t) * sinh (b * t) ≤ sinh (a * t) := by
  have hratio : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hc := convexOn_exp.2 (Set.mem_univ (-2 * (b * t))) (Set.mem_univ (0 : ℝ))
    (div_nonneg ha hb.le) (sub_nonneg.mpr hratio)
    (by ring : a / b + (1 - a / b) = 1)
  have har : (a / b) * (-2 * (b * t)) + (1 - a / b) * 0 = -2 * (a * t) := by
    field_simp
    ring
  change exp ((a / b) * (-2 * (b * t)) + (1 - a / b) * 0) ≤
    (a / b) * exp (-2 * (b * t)) + (1 - a / b) * exp 0 at hc
  rw [har, exp_zero, mul_one] at hc
  have hs (z : ℝ) : sinh z = exp z * (1 - exp (-2 * z)) / 2 := by
    rw [sinh_eq, mul_sub, mul_one, ← exp_add, show z + -2 * z = -z by ring]
  have he : exp (-(b - a) * t) * exp (b * t) = exp (a * t) := by
    rw [← exp_add, show -(b - a) * t + b * t = a * t by ring]
  have hi : a / b * (1 - exp (-2 * (b * t))) ≤ 1 - exp (-2 * (a * t)) := by
    linarith
  calc
    _ = (exp (a * t) / 2) * (a / b * (1 - exp (-2 * (b * t)))) := by
      rw [hs]
      calc
        _ = (exp (-(b - a) * t) * exp (b * t) / 2) *
            (a / b * (1 - exp (-2 * (b * t)))) := by ring
        _ = _ := by rw [he]
    _ ≤ (exp (a * t) / 2) * (1 - exp (-2 * (a * t))) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [hs]; ring

private theorem hasDerivAt_degreePrimitive (n : ℕ) (t : ℝ) :
    HasDerivAt (degreePrimitive n) (cosh (((n : ℝ) + 1) * t) - cosh t) t := by
  change HasDerivAt ((fun z : ℝ ↦ sinh (((n : ℝ) + 1) * z) / ((n : ℝ) + 1)) - sinh)
    (cosh (((n : ℝ) + 1) * t) - cosh t) t
  have h := (((hasDerivAt_id' t).const_mul ((n : ℝ) + 1)).sinh.div_const
    ((n : ℝ) + 1)).sub (hasDerivAt_sinh t)
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simpa only [mul_one, mul_div_cancel_right₀ _ hn] using h

private theorem cosh_degree_difference (n : ℕ) (t : ℝ) :
    cosh (((n : ℝ) + 1) * t) - cosh t =
      2 * sinh (((n : ℝ) + 2) / 2 * t) * sinh ((n : ℝ) / 2 * t) := by
  let u := ((n : ℝ) + 2) / 2 * t
  let v := (n : ℝ) / 2 * t
  have h₁ : ((n : ℝ) + 1) * t = u + v := by dsimp [u, v]; ring
  have h₂ : t = u - v := by dsimp [u, v]; ring
  change cosh (((n : ℝ) + 1) * t) - cosh t = 2 * sinh u * sinh v
  rw [h₁, h₂, cosh_add, cosh_sub]
  ring

/-- The ratio of the deficits at two degrees is bounded below by the
cubic degree factor and the exponential of their difference. -/
theorem twoNodeDeficit_degree_lower {j p : ℕ} (hjp : j ≤ p) (hp : 0 < p)
    {x : ℝ} (hx : 0 ≤ x) :
    twoNodeDeficit p x *
        (((j : ℝ) + 1) * (j : ℝ) * ((j : ℝ) + 2) /
          (((p : ℝ) + 1) * (p : ℝ) * ((p : ℝ) + 2))) *
        exp (-((p : ℝ) - (j : ℝ)) * x) ≤ twoNodeDeficit j x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [twoNodeDeficit_at_zero]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hjp' : (j : ℝ) ≤ p := by exact_mod_cast hjp
  have hj : (0 : ℝ) ≤ j := by positivity
  let q : ℝ := (j : ℝ) * ((j : ℝ) + 2) / ((p : ℝ) * ((p : ℝ) + 2))
  let m : ℝ := q * exp (-((p : ℝ) - (j : ℝ)) * x)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 x) :
      m * (cosh (((p : ℝ) + 1) * t) - cosh t) ≤ cosh (((j : ℝ) + 1) * t) - cosh t := by
    have ht0 := ht.1
    have ha := scaled_sinh_lower (a := ((j : ℝ) + 2) / 2) (b := ((p : ℝ) + 2) / 2)
      (t := t) (by positivity) (by linarith) (by positivity)
    have hb := scaled_sinh_lower (a := (j : ℝ) / 2) (b := (p : ℝ) / 2)
      (t := t) (by positivity) (by linarith) (by positivity)
    have hmul := mul_le_mul ha hb
      (mul_nonneg (by positivity) (sinh_nonneg_iff.mpr (by positivity)))
      (sinh_nonneg_iff.mpr (by positivity))
    have hform :
        (((j : ℝ) + 2) / 2 / (((p : ℝ) + 2) / 2) *
          exp (-(((p : ℝ) + 2) / 2 - ((j : ℝ) + 2) / 2) * t) *
          sinh (((p : ℝ) + 2) / 2 * t)) *
        ((j : ℝ) / 2 / ((p : ℝ) / 2) *
          exp (-((p : ℝ) / 2 - (j : ℝ) / 2) * t) * sinh ((p : ℝ) / 2 * t)) =
        (q * exp (-((p : ℝ) - (j : ℝ)) * t)) *
          (sinh (((p : ℝ) + 2) / 2 * t) * sinh ((p : ℝ) / 2 * t)) := by
      have he : exp (-(((p : ℝ) + 2) / 2 - ((j : ℝ) + 2) / 2) * t) *
          exp (-((p : ℝ) / 2 - (j : ℝ) / 2) * t) = exp (-((p : ℝ) - (j : ℝ)) * t) := by
        rw [← exp_add]
        congr 1
        ring
      calc
        _ = ((((j : ℝ) + 2) / 2 / (((p : ℝ) + 2) / 2)) * ((j : ℝ) / 2 / ((p : ℝ) / 2))) *
            (exp (-(((p : ℝ) + 2) / 2 - ((j : ℝ) + 2) / 2) * t) *
              exp (-((p : ℝ) / 2 - (j : ℝ) / 2) * t)) *
            (sinh (((p : ℝ) + 2) / 2 * t) * sinh ((p : ℝ) / 2 * t)) := by ring
        _ = _ := by
          rw [he]
          dsimp [q]
          field_simp [hp'.ne']
    rw [hform] at hmul
    have hexp : exp (-((p : ℝ) - (j : ℝ)) * x) ≤ exp (-((p : ℝ) - (j : ℝ)) * t) :=
      exp_le_exp.mpr (by
        simpa only [neg_mul, neg_le_neg_iff] using
          mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hjp'))
    rw [cosh_degree_difference, cosh_degree_difference]
    dsimp [m]
    have hq : 0 ≤ q := by positivity
    have hs : 0 ≤ sinh (((p : ℝ) + 2) / 2 * t) * sinh ((p : ℝ) / 2 * t) :=
      mul_nonneg (sinh_nonneg_iff.mpr (by positivity)) (sinh_nonneg_iff.mpr (by positivity))
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hq) hs
    nlinarith only [he.trans hmul]
  let f (t : ℝ) := degreePrimitive j t - m * degreePrimitive p t
  have hd (t : ℝ) : HasDerivAt f
      ((cosh (((j : ℝ) + 1) * t) - cosh t) -
        m * (cosh (((p : ℝ) + 1) * t) - cosh t)) t :=
    (hasDerivAt_degreePrimitive j t).sub ((hasDerivAt_degreePrimitive p t).const_mul m)
  have hmono : MonotoneOn f (Set.Icc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [(hd t).deriv]
    exact sub_nonneg.mpr (hpoint t (interior_subset ht))
  have hfx : 0 ≤ f x := by
    have h := hmono ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx.le
    simpa [f, degreePrimitive] using h
  have hz : m * degreePrimitive p x ≤ degreePrimitive j x := sub_nonneg.mp hfx
  rw [twoNodeDeficit_eq_primitive p hx, twoNodeDeficit_eq_primitive j hx]
  calc
    _ = (((j : ℝ) + 1) / sinh x) * (m * degreePrimitive p x) := by
      dsimp [m, q]
      field_simp [(sinh_pos_iff.mpr hx).ne', hp'.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)

end
end RefinedBMV.Tracial
