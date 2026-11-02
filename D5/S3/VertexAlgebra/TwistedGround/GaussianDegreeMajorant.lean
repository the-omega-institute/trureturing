/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A creation recurrence gives a uniform all-degree mass bound. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
This is the analytic lemma for the CCR proof of squeezed-vacuum summability.
Its hypothesis is a scalar recurrence, not a Gaussian norm formula, a bound
on partial sums, or summability. FactorialFockQuadraticEstimate derives that
recurrence from polynomial creation and differentiation. Every manipulation
before the last two theorems is finite; no power-series interchange occurs.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant

private def partialMass (a : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), a n * t ^ n

private def slope (a : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℝ) * a (n + 1) * t ^ n

private theorem partial_hasDeriv (a : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (partialMass a N) (slope a N t) t := by
  induction N with
  | zero =>
    convert hasDerivAt_const t (a 0) using 1
    · funext x
      simp [partialMass]
    · simp [slope]
  | succ N ih =>
    have hp := ((hasDerivAt_id t).pow (N + 1)).const_mul (a (N + 1))
    have hf : partialMass a (N + 1) =
        (fun x => partialMass a N x + a (N + 1) * x ^ (N + 1)) := by
      funext x
      exact Finset.sum_range_succ _ (N + 1)
    rw [hf]
    convert ih.add hp using 1 <;> (try rfl)
    simp only [slope, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, mul_one, id_eq]
    ring

private theorem partial_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ partialMass a N t :=
  Finset.sum_nonneg (fun n _ => mul_nonneg (ha n) (pow_nonneg ht n))

private theorem slope_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ slope a N t := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (mul_nonneg (by positivity) (ha _)) (pow_nonneg ht _)

private theorem partial_step (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : partialMass a N t ≤ partialMass a (N + 1) t := by
  simp only [partialMass, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (mul_nonneg (ha _) (pow_nonneg ht _))

private theorem slope_step (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : slope a N t ≤ slope a (N + 1) t := by
  rw [slope, slope, Finset.sum_range_succ]
  exact le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (by positivity) (ha _)) (pow_nonneg ht _))

private theorem weighted_sum (a : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range (N + 1), (n : ℝ) * a n * t ^ n) = t * slope a N t := by
  induction N with
  | zero => simp [slope]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [slope, Finset.sum_range_succ, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

private theorem derivative_le (a : ℕ → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hr1 : r < 1) (ha : ∀ n, 0 ≤ a n)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤ (c + r * n) * a n)
    (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    slope a N t ≤ (c / (1 - r)) * partialMass a N t := by
  have hd : 0 < 1 - r := sub_pos.mpr hr1
  have hC : 0 ≤ c / (1 - r) := div_nonneg hc hd.le
  cases N with
  | zero => simpa [slope] using mul_nonneg hC (partial_nonneg a ha 0 ht.1)
  | succ N =>
    have he : slope a (N + 1) t ≤
        c * partialMass a N t + r * t * slope a N t := by
      calc
        _ ≤ ∑ n ∈ Finset.range (N + 1), (c + r * n) * a n * t ^ n := by
          apply Finset.sum_le_sum
          intro n hn
          exact mul_le_mul_of_nonneg_right (hrec n) (pow_nonneg ht.1 n)
        _ = c * partialMass a N t +
            r * (∑ n ∈ Finset.range (N + 1), (n : ℝ) * a n * t ^ n) := by
          simp only [partialMass, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by rw [weighted_sum]; ring
    have he' : slope a (N + 1) t ≤
        c * partialMass a (N + 1) t + r * slope a (N + 1) t := by
      calc
        _ ≤ c * partialMass a N t + r * t * slope a N t := he
        _ ≤ c * partialMass a (N + 1) t + r * t * slope a (N + 1) t := by
          exact add_le_add (mul_le_mul_of_nonneg_left (partial_step a ha N ht.1) hc)
            (mul_le_mul_of_nonneg_left (slope_step a ha N ht.1) (mul_nonneg hr ht.1))
        _ ≤ c * partialMass a (N + 1) t + r * slope a (N + 1) t := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_right _ (slope_nonneg a ha (N + 1) ht.1)
          simpa using mul_le_mul_of_nonneg_left ht.2 hr
    have hh : slope a (N + 1) t * (1 - r) ≤ c * partialMass a (N + 1) t := by
      nlinarith
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hd).2 hh

/-- All particle cutoffs have the SAME constant. No sum bound is a premise. -/
theorem partial_sum_bound (a : ℕ → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hr1 : r < 1) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤ (c + r * n) * a n)
    (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n) ≤ Real.exp (c / (1 - r)) := by
  let C : ℝ := c / (1 - r)
  let F : ℝ → ℝ := fun t => Real.exp (-C * t) * partialMass a N t
  have hd (t : ℝ) : HasDerivAt F
      (Real.exp (-C * t) * (slope a N t - C * partialMass a N t)) t := by
    convert (((hasDerivAt_id t).const_mul (-C)).exp).mul
      (partial_hasDeriv a N t) using 1 <;>
      first | rfl | (funext x; dsimp [F]; ring) | (dsimp [F]; ring)
  have hanti : AntitoneOn F (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      ((show Differentiable ℝ F from fun t => (hd t).differentiableAt).continuous.continuousOn)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (derivative_le a hc hr hr1 ha hrec N ht'))
  have he : Real.exp (-C) * partialMass a N 1 ≤ 1 := by
    have h := hanti (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
      (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
    simpa [F, partialMass, Finset.sum_range_succ', ha0] using h
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos C).le
  rw [← mul_assoc, ← Real.exp_add] at hm
  simpa [partialMass, C] using hm

/-- The recurrence proves genuine summability over ALL particle numbers. -/
theorem summable_of_creation_recurrence (a : ℕ → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hr1 : r < 1) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤ (c + r * n) * a n) :
    Summable a := by
  apply summable_of_sum_range_le ha (c := Real.exp (c / (1 - r)))
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), a n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
        (fun n _ _ => ha n)
    _ ≤ _ := partial_sum_bound a hc hr hr1 ha ha0 hrec N

theorem tsum_bound (a : ℕ → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hr1 : r < 1) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤ (c + r * n) * a n) :
    (∑' n, a n) ≤ Real.exp (c / (1 - r)) := by
  apply Real.tsum_le_of_sum_range_le ha
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), a n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
        (fun n _ _ => ha n)
    _ ≤ _ := partial_sum_bound a hc hr hr1 ha ha0 hrec N

end D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant
