/- GID: D5/S3/StatisticalMechanics/DelayedCooling/Kernel
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DelayedCooling/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete delayed relaxation and its differential equation. -/

module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-!
# The quasi-exponential relaxation

The extension to negative times is the constant equilibrium history. The
cutoff-power representation agrees with the finite sum in Santos, Eq. (6),
and permits local finite-sum calculations at the step boundaries.
-/

public section

namespace D5.S3.StatisticalMechanics.DelayedCooling.Kernel

open Set Filter
open scoped Topology BigOperators

noncomputable section

private def cutPower (n : ℕ) (x : ℝ) : ℝ := min x 0 ^ (n + 1)

private theorem continuous_cutPower (n : ℕ) : Continuous (cutPower n) := by
  exact (continuous_id.min continuous_const).pow _

private theorem hasDerivAt_cutPower_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (cutPower (n + 1)) ((n + 2 : ℕ) * min x 0 ^ (n + 1)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := (hasDerivAt_id x).fun_pow (n + 2)
    convert h.congr_of_eventuallyEq ?_ using 1
    · simp [min_eq_left hx.le, show n + 2 - 1 = n + 1 by omega]
    · filter_upwards [Iio_mem_nhds hx] with y hy
      simp [cutPower, min_eq_left (le_of_lt (mem_Iio.mp hy)), Nat.add_assoc]
  · have hl : HasDerivWithinAt (cutPower (n + 1)) 0 (Iic 0) 0 := by
      have hp : HasDerivAt (fun x : ℝ => x ^ (n + 2)) 0 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).fun_pow (n + 2)
      exact hp.hasDerivWithinAt.congr
        (fun y hy => by simp [cutPower, min_eq_left (mem_Iic.mp hy), Nat.add_assoc])
        (by simp [cutPower])
    have hr : HasDerivWithinAt (cutPower (n + 1)) 0 (Ici 0) 0 := by
      exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
        (fun y hy => by simp [cutPower, min_eq_right (mem_Ici.mp hy), Nat.add_assoc])
        (by simp [cutPower])
    simpa [Iic_union_Ici] using hl.union hr
  · have h := hasDerivAt_const x (0 : ℝ)
    convert h.congr_of_eventuallyEq ?_ using 1
    · simp [min_eq_right hx.le]
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [cutPower, min_eq_right (le_of_lt (mem_Ioi.mp hy))]

/-- A cutoff summand in the source finite sum. -/
private def term (τ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  cutPower n ((n : ℝ) * τ - t) / (n + 1).factorial

private def stepSum (τ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  1 + ∑ n ∈ Finset.range N, term τ n t

/-- The source quasi-exponential, including its constant negative-time history. -/
def relaxation (τ t : ℝ) : ℝ := stepSum τ (⌊t / τ⌋₊ + 1) t

private theorem term_eq_zero {τ t : ℝ} {n : ℕ} (h : t ≤ (n : ℝ) * τ) :
    term τ n t = 0 := by
  simp [term, cutPower, min_eq_right (sub_nonneg.mpr h)]

private theorem stepSum_stable {τ t : ℝ} (hτ : 0 < τ) {N M : ℕ}
    (hNM : N ≤ M) (ht : t ≤ (N : ℝ) * τ) : stepSum τ M t = stepSum τ N t := by
  unfold stepSum
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n hn hnN
  apply term_eq_zero
  have hNn : N ≤ n := by simpa using hnN
  exact ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hNn) hτ.le)

private theorem relaxation_eq_stepSum {τ t : ℝ} (hτ : 0 < τ) {N : ℕ}
    (ht : t ≤ (N : ℝ) * τ) : relaxation τ t = stepSum τ N t := by
  have hf : t ≤ ((⌊t / τ⌋₊ + 1 : ℕ) : ℝ) * τ := by
    have := Nat.lt_floor_add_one (t / τ)
    exact ((div_lt_iff₀ hτ).mp (by simpa using this)).le
  unfold relaxation
  rcases le_total N (⌊t / τ⌋₊ + 1) with h | h
  · exact stepSum_stable hτ h ht
  · exact (stepSum_stable hτ h hf).symm

private theorem relaxation_eventually_stepSum {τ t : ℝ} (hτ : 0 < τ) {N : ℕ}
    (ht : t < (N : ℝ) * τ) : relaxation τ =ᶠ[𝓝 t] stepSum τ N := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact relaxation_eq_stepSum hτ hs.le

/-- The literal finite sum of source Eq. (6), for every nonnegative real time. -/
theorem relaxation_eq_source_sum {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    relaxation τ t =
      1 + ∑ n ∈ Finset.range (⌊t / τ⌋₊ + 1),
        (((n : ℝ) * τ - t) ^ (n + 1)) / (n + 1).factorial := by
  unfold relaxation stepSum
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ ⌊t / τ⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hnt : (n : ℝ) * τ ≤ t := by
    exact (le_div_iff₀ hτ).mp ((Nat.cast_le.mpr hn').trans (Nat.floor_le (div_nonneg ht hτ.le)))
  simp [term, cutPower, min_eq_left (sub_nonpos.mpr hnt)]

/-- Negative times retain the equilibrated value, including the value at zero. -/
theorem relaxation_of_nonpos {τ t : ℝ} (hτ : 0 < τ) (ht : t ≤ 0) :
    relaxation τ t = 1 := by
  rw [relaxation_eq_stepSum hτ (N := 0) (by simpa using ht)]
  simp [stepSum]

private theorem continuous_stepSum (τ : ℝ) (N : ℕ) : Continuous (stepSum τ N) := by
  unfold stepSum term
  exact continuous_const.add (continuous_finsetSum _ (fun n _ =>
    ((continuous_cutPower n).comp (continuous_const.sub continuous_id)).div_const _))

/-- All step boundaries glue continuously, including the equilibrium endpoint. -/
theorem continuous_relaxation {τ : ℝ} (hτ : 0 < τ) : Continuous (relaxation τ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : t < ((⌊t / τ⌋₊ + 1 : ℕ) : ℝ) * τ := by
    exact (div_lt_iff₀ hτ).mp (by simpa using Nat.lt_floor_add_one (t / τ))
  exact (continuous_stepSum τ _).continuousAt.congr
    (relaxation_eventually_stepSum hτ ht).symm

private theorem hasDerivAt_term_zero (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (term τ 0) (-1) t := by
  apply (hasDerivAt_neg t).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp [term, cutPower, min_eq_left (neg_nonpos.mpr (mem_Ioi.mp hs).le)]

private theorem hasDerivAt_term_succ (τ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (term τ (n + 1)) (-term τ n (t - τ)) t := by
  have h := ((hasDerivAt_cutPower_succ n (((n + 1 : ℕ) : ℝ) * τ - t)).comp t
    ((hasDerivAt_const t (((n + 1 : ℕ) : ℝ) * τ)).sub (hasDerivAt_id t))).div_const
      (((n + 2).factorial : ℕ) : ℝ)
  change HasDerivAt (term τ (n + 1)) _ t at h
  convert h using 1
  unfold term cutPower
  have he : ((n + 1 : ℕ) : ℝ) * τ - t = (n : ℝ) * τ - (t - τ) := by
    push_cast
    ring
  rw [he, Nat.factorial_succ (n + 1)]
  push_cast
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem hasDerivAt_stepSum (τ : ℝ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (stepSum τ (N + 1)) (-stepSum τ N (t - τ)) t := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => hasDerivAt_term_succ τ n t)
  have h := (hasDerivAt_const t (1 : ℝ)).add
    (hsum.add (hasDerivAt_term_zero τ ht))
  convert h using 1
  · ext s
    simp [stepSum, Finset.sum_range_succ']
  · simp [stepSum, ← Finset.sum_neg_distrib]

/-- The delayed differential equation holds at every strictly positive real time,
including all positive step boundaries. No differentiability at zero is asserted. -/
theorem hasDerivAt_relaxation {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t) :
    HasDerivAt (relaxation τ) (-relaxation τ (t - τ)) t := by
  let N := ⌊t / τ⌋₊ + 1
  have hN : t < (N : ℝ) * τ :=
    (div_lt_iff₀ hτ).mp (by simpa [N] using Nat.lt_floor_add_one (t / τ))
  have hNp : t < ((N + 1 : ℕ) : ℝ) * τ := by
    push_cast
    linarith
  have hshift : t - τ ≤ (N : ℝ) * τ := by linarith
  rw [relaxation_eq_stepSum hτ hshift]
  exact (hasDerivAt_stepSum τ N ht).congr_of_eventuallyEq
    (relaxation_eventually_stepSum hτ hNp)

end

end D5.S3.StatisticalMechanics.DelayedCooling.Kernel
