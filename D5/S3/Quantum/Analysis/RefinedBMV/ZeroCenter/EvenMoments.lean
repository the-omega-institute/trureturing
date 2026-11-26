/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/EvenMoments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A four-term even-moment lower bound for the zero-centered geometric profile. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The four even moments of the centered finite arithmetic progression. -/

open scoped BigOperators

noncomputable section

namespace RefinedBMV.FourSpectrumLift

/-- The geometric-sum term of the normalized zero-centered profile. -/
def zeroCenterGeometricSum (p : ℕ) (c : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (p + 1), Real.exp (-3 * c / (p : ℝ)) ^ j) /
    (((p : ℝ) + 1) * Real.exp (-3 * c / 2))

/-- The even-moment polynomial used by the small-gap cover, at reciprocal degree `h`. -/
def zeroCenterEvenMomentLower (c h : ℝ) : ℝ :=
  let m₂ := 3 * (1 + 2 * h) / 4
  let m₄ := 27 * (1 + 2 * h) * (3 + 6 * h - 4 * h ^ 2) / 80
  let m₆ := 243 * (1 + 2 * h) * (3 + 12 * h - 24 * h ^ 3 + 16 * h ^ 4) / 448
  let m₈ := 729 * (1 + 2 * h) *
    (5 + 30 * h + 20 * h ^ 2 - 120 * h ^ 3 - 16 * h ^ 4 + 288 * h ^ 5 - 192 * h ^ 6) / 1280
  m₂ + c ^ 2 * (m₄ / 2 + c ^ 2 * (m₆ / 24 + c ^ 2 * m₈ / 720))

private def centeredMoment (p n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (p + 1), ((p : ℝ) - 2 * (j : ℝ)) ^ n

private theorem centeredMoment_add_two (p k : ℕ) :
    centeredMoment (p + 2) (2 * k) =
      centeredMoment p (2 * k) + 2 * ((p + 2 : ℕ) : ℝ) ^ (2 * k) := by
  let x : ℝ := ((p + 2 : ℕ) : ℝ)
  let f (j : ℕ) : ℝ := (x - 2 * (j : ℝ)) ^ (2 * k)
  change (∑ j ∈ Finset.range ((p + 2) + 1), f j) = centeredMoment p (2 * k) + 2 * x ^ (2 * k)
  rw [Finset.sum_range_succ f (p + 2), Finset.sum_range_succ' f (p + 1)]
  have hmiddle : (∑ j ∈ Finset.range (p + 1), f (j + 1)) = centeredMoment p (2 * k) := by
    unfold centeredMoment
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only [f, x]
    rw [show ((p + 2 : ℕ) : ℝ) - 2 * ((j + 1 : ℕ) : ℝ) = (p : ℝ) - 2 * (j : ℝ) by
      push_cast
      ring]
  have hfirst : f 0 = x ^ (2 * k) := by simp [f]
  have hlast : f (p + 2) = x ^ (2 * k) := by
    change (x - 2 * x) ^ (2 * k) = x ^ (2 * k)
    rw [show x - 2 * x = -x by ring, (even_two_mul k).neg_pow]
  rw [hmiddle, hfirst, hlast]
  ring

private theorem centeredMoment_polynomials (p : ℕ) :
    let x : ℝ := p
    centeredMoment p 2 = x * (x + 1) * (x + 2) * (1 / 3) ∧
    centeredMoment p 4 = x * (x + 1) * (x + 2) * ((3 * x ^ 2 + 6 * x - 4) / 15) ∧
    centeredMoment p 6 = x * (x + 1) * (x + 2) *
      ((3 * x ^ 4 + 12 * x ^ 3 - 24 * x + 16) / 21) ∧
    centeredMoment p 8 = x * (x + 1) * (x + 2) *
      ((5 * x ^ 6 + 30 * x ^ 5 + 20 * x ^ 4 - 120 * x ^ 3 - 16 * x ^ 2 + 288 * x - 192) / 45) := by
  induction p using Nat.twoStepInduction with
  | zero => norm_num [centeredMoment, Finset.sum_range_succ]
  | one => norm_num [centeredMoment, Finset.sum_range_succ]
  | more p ih _ =>
      obtain ⟨h₂, h₄, h₆, h₈⟩ := ih
      have hs₂ := centeredMoment_add_two p 1
      have hs₄ := centeredMoment_add_two p 2
      have hs₆ := centeredMoment_add_two p 3
      have hs₈ := centeredMoment_add_two p 4
      simp only [Nat.reduceMul] at hs₂ hs₄ hs₆ hs₈
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hs₂, h₂]
        push_cast
        ring
      · rw [hs₄, h₄]
        push_cast
        ring
      · rw [hs₆, h₆]
        push_cast
        ring
      · rw [hs₈, h₈]
        push_cast
        ring

private theorem cosh_four_term_lower (x : ℝ) :
    1 + x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 720 ≤ Real.cosh x := by
  have hs := Real.hasSum_cosh x
  have h := hs.summable.sum_le_tsum (Finset.range 4) (fun n _ ↦
    div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) n) (by positivity))
  rw [hs.tsum_eq] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact h

/-- The second derivative of the normalized geometric sum dominates the small-gap
cover polynomial at every positive integer degree and every real gap. -/
theorem zeroCenterEvenMomentLower_le_deriv2 {p : ℕ} (hp : 0 < p) (c : ℝ) :
    zeroCenterEvenMomentLower c (1 / (p : ℝ)) ≤ deriv^[2] (zeroCenterGeometricSum p) c := by
  let h : ℝ := 1 / (p : ℝ)
  let N : ℝ := (p : ℝ) + 1
  let a : ℝ := 3 / (2 * (p : ℝ))
  let g (j : ℕ) : ℝ := a * ((p : ℝ) - 2 * (j : ℝ))
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hN : 0 < N := by dsimp only [N]; positivity
  have hp₁ : (p : ℝ) + 1 ≠ 0 := hN.ne'
  have hgeom : zeroCenterGeometricSum p =
      fun x ↦ (∑ j ∈ Finset.range (p + 1), Real.exp (g j * x)) / N := by
    funext x
    rw [zeroCenterGeometricSum, div_mul_eq_div_div_swap]
    apply congrArg (fun y : ℝ ↦ y / N)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    dsimp only [g, a]
    field_simp [hp'] <;> ring
  have hexp (j : ℕ) (x : ℝ) :
      HasDerivAt (fun t ↦ Real.exp (g j * t)) (g j * Real.exp (g j * x)) x := by
    have hlinear : HasDerivAt (fun t ↦ g j * t) (g j) x := by
      simpa only [mul_one] using (hasDerivAt_id' x).const_mul (g j)
    rw [mul_comm (g j) (Real.exp (g j * x))]
    exact hlinear.exp
  have hfirst :
      deriv (fun x ↦ (∑ j ∈ Finset.range (p + 1), Real.exp (g j * x)) / N) =
        fun x ↦ (∑ j ∈ Finset.range (p + 1), g j * Real.exp (g j * x)) / N := by
    funext x
    exact ((HasDerivAt.fun_sum (u := Finset.range (p + 1)) (fun j _ ↦ hexp j x)).div_const N).deriv
  have hsecond :
      deriv (fun x ↦ (∑ j ∈ Finset.range (p + 1), g j * Real.exp (g j * x)) / N) c =
        (∑ j ∈ Finset.range (p + 1), g j ^ 2 * Real.exp (g j * c)) / N := by
    have hsum : HasDerivAt (fun x ↦ ∑ j ∈ Finset.range (p + 1), g j * Real.exp (g j * x))
        (∑ j ∈ Finset.range (p + 1), g j ^ 2 * Real.exp (g j * c)) c := by
      refine HasDerivAt.fun_sum (fun j _ ↦ ?_)
      convert (hexp j c).const_mul (g j) using 1 <;> ring
    exact (hsum.div_const N).deriv
  have hreflect (j : ℕ) (hj : j ∈ Finset.range (p + 1)) : g (p - j) = -g j := by
    dsimp only [g]
    rw [Nat.cast_sub (Finset.mem_range_succ_iff.mp hj)]
    ring
  have hswap :
      (∑ j ∈ Finset.range (p + 1), g j ^ 2 * Real.exp (-(g j * c))) =
        ∑ j ∈ Finset.range (p + 1), g j ^ 2 * Real.exp (g j * c) := by
    calc
      _ = ∑ j ∈ Finset.range (p + 1), g (p - j) ^ 2 * Real.exp (g (p - j) * c) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [hreflect j hj, neg_sq, neg_mul]
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          Finset.sum_range_reflect (fun j ↦ g j ^ 2 * Real.exp (g j * c)) (p + 1)
  have hcosh :
      (∑ j ∈ Finset.range (p + 1), g j ^ 2 * Real.cosh (g j * c)) =
        ∑ j ∈ Finset.range (p + 1), g j ^ 2 * Real.exp (g j * c) := by
    simp only [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Finset.sum_div,
      Finset.sum_add_distrib, hswap] <;> ring
  let moment (n : ℕ) : ℝ := (∑ j ∈ Finset.range (p + 1), g j ^ n) / N
  have hbound :
      moment 2 + c ^ 2 * (moment 4 / 2 + c ^ 2 * (moment 6 / 24 + c ^ 2 * moment 8 / 720)) ≤
        (∑ j ∈ Finset.range (p + 1), g j ^ 2 * Real.cosh (g j * c)) / N := by
    calc
      _ = (∑ j ∈ Finset.range (p + 1),
        (g j ^ 2 + g j ^ 4 * (c ^ 2 / 2) + g j ^ 6 * (c ^ 4 / 24) +
          g j ^ 8 * (c ^ 6 / 720))) / N := by
          simp only [moment, Finset.sum_add_distrib, ← Finset.sum_mul]
          ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hN.le
        refine Finset.sum_le_sum fun j _ ↦ ?_
        convert mul_le_mul_of_nonneg_left (cosh_four_term_lower (g j * c)) (sq_nonneg (g j))
          using 1 <;> ring
  have hscale (n : ℕ) : moment n = a ^ n * centeredMoment p n / N := by
    unfold moment centeredMoment
    rw [Finset.mul_sum]
    apply congrArg (fun y : ℝ ↦ y / N)
    exact Finset.sum_congr rfl fun j _ ↦ mul_pow _ _ _
  obtain ⟨h₂, h₄, h₆, h₈⟩ := centeredMoment_polynomials p
  have hm₂ : moment 2 = 3 * (1 + 2 * h) / 4 := by
    rw [hscale, h₂]
    dsimp only [a, N, h]
    field_simp [hp', hp₁] <;> ring
  have hm₄ : moment 4 = 27 * (1 + 2 * h) * (3 + 6 * h - 4 * h ^ 2) / 80 := by
    rw [hscale, h₄]
    dsimp only [a, N, h]
    field_simp [hp', hp₁] <;> ring
  have hm₆ : moment 6 = 243 * (1 + 2 * h) * (3 + 12 * h - 24 * h ^ 3 + 16 * h ^ 4) / 448 := by
    rw [hscale, h₆]
    dsimp only [a, N, h]
    field_simp [hp', hp₁] <;> ring
  have hm₈ : moment 8 = 729 * (1 + 2 * h) *
      (5 + 30 * h + 20 * h ^ 2 - 120 * h ^ 3 - 16 * h ^ 4 + 288 * h ^ 5 - 192 * h ^ 6) / 1280 := by
    rw [hscale, h₈]
    dsimp only [a, N, h]
    field_simp [hp', hp₁] <;> ring
  change zeroCenterEvenMomentLower c h ≤ deriv (deriv (zeroCenterGeometricSum p)) c
  rw [hgeom, hfirst, hsecond, ← hcosh]
  simpa only [zeroCenterEvenMomentLower, hm₂, hm₄, hm₆, hm₈] using hbound

#print axioms zeroCenterEvenMomentLower_le_deriv2

end RefinedBMV.FourSpectrumLift
