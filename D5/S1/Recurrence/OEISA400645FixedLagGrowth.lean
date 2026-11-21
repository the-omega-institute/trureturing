/- GID: D5/S1/Recurrence/OEISA400645FixedLagGrowth
   generality: I
   mirror-B: D5/B/S1/Recurrence/OEISA400645FixedLagGrowth
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Analysis.Asymptotics.SpecificAsymptotics]
   utility: none
   digest: A400645 source sequences have fixed-lag ratio limits and logarithmic growth log λ. -/

import D5.S1.Recurrence.OEISA400645
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Fixed-lag ratios and logarithmic growth of the A400645 source sequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.OEISA400645FixedLagGrowth

open Filter Topology D5.S1.Recurrence.OEISA400645

private theorem lam_pos : 0 < limitingRatio := by
  unfold limitingRatio squaredLimit
  apply Real.sqrt_pos.mpr
  positivity

private theorem ratio {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 limitingRatio) := by
  rw [Metric.tendsto_atTop]
  intro ε he
  obtain ⟨N, -, hN⟩ := result.2.1 a ha ε he
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using (hN n hn).2⟩

private theorem pos_eventually {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    ∀ᶠ n in atTop, (0 : ℝ) < a n := by
  obtain ⟨N, -, hN⟩ := result.2.1 a ha 1 one_pos
  filter_upwards [eventually_ge_atTop N] with n hn
  exact_mod_cast (hN n hn).1

private theorem lag {a : ℕ → ℕ} (ha : IsSourceSequence a) (h : ℕ) :
    Tendsto (fun n => (a (n + h) : ℝ) / a n) atTop (𝓝 (limitingRatio ^ h)) := by
  induction h with
  | zero =>
    simp only [Nat.add_zero, pow_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [pos_eventually ha] with n hn
    exact (div_self hn.ne').symm
  | succ h ih =>
    have hr := (ratio ha).comp (tendsto_add_atTop_nat h)
    have hm := hr.mul ih
    rw [mul_comm] at hm
    rw [pow_succ]
    apply (hm.congr' _)
    filter_upwards [(tendsto_add_atTop_nat h).eventually (pos_eventually ha)] with n hn
    simp only [Function.comp_apply] at *
    rw [show n + (h + 1) = n + h + 1 by ring]
    field_simp

private theorem log_growth {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    Tendsto (fun n => Real.log (a n) / n) atTop (𝓝 (Real.log limitingRatio)) := by
  obtain ⟨N, hN4, hN⟩ := result.2.1 a ha 1 one_pos
  have hpos : ∀ n, N ≤ n → (0 : ℝ) < a n := fun n hn => by exact_mod_cast (hN n hn).1
  let u : ℕ → ℝ := fun k => Real.log ((a (k + N + 1) : ℝ) / a (k + N))
  have hu : Tendsto u atTop (𝓝 (Real.log limitingRatio)) :=
    ((Real.continuousAt_log lam_pos.ne').tendsto).comp
      ((ratio ha).comp (tendsto_add_atTop_nat N)) |>.congr (fun k => by
        simp [u, Function.comp_apply])
  have hc := hu.cesaro
  have htel : ∀ n, ∑ i ∈ Finset.range n, u i = Real.log (a (n + N)) - Real.log (a N) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [u]
      rw [Real.log_div (hpos _ (by omega)).ne' (hpos _ (by omega)).ne',
        show n + 1 + N = n + N + 1 by ring]
      ring
  have h1 : Tendsto (fun n : ℕ => (Real.log (a (n + N)) - Real.log (a N)) / n) atTop
      (𝓝 (Real.log limitingRatio)) := by
    refine hc.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← htel n, div_eq_inv_mul]
  have h2 : Tendsto (fun n : ℕ => Real.log (a N) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) / (n + N : ℕ)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) / (1 + (N : ℝ) / n)) atTop (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)) (by norm_num)
    rw [show (1 : ℝ) / (1 + 0) = 1 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
  have h4 := ((h1.add h2).mul h3)
  rw [add_zero, mul_one] at h4
  have h5 : Tendsto (fun n : ℕ => Real.log (a (n + N)) / (n + N : ℕ)) atTop
      (𝓝 (Real.log limitingRatio)) := by
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
    ring
  exact (tendsto_add_atTop_iff_nat N).1 h5

/-- Every A400645 source sequence has fixed-lag ratios `a (n + h) / a n → λ ^ h` for every
`h`, including `h = 0`, and logarithmic growth `log (a n) / n → log λ`. -/
theorem result :
    ∀ a : ℕ → ℕ, IsSourceSequence a →
      (∀ h : ℕ, Tendsto (fun n => (a (n + h) : ℝ) / a n) atTop (𝓝 (limitingRatio ^ h))) ∧
        Tendsto (fun n => Real.log (a n) / n) atTop (𝓝 (Real.log limitingRatio)) :=
  fun _ ha => ⟨lag ha, log_growth ha⟩

end D5.S1.Recurrence.OEISA400645FixedLagGrowth
