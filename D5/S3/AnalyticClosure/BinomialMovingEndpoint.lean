/- GID: D5/S3/AnalyticClosure/BinomialMovingEndpoint
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialMovingEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moving lower endpoints of weighted binomial power sums. -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Real Finset
open scoped Topology

namespace D5.S3.AnalyticClosure.BinomialMovingEndpoint

/-- The lower sum of weighted binomial powers is asymptotic to its endpoint
term times a geometric factor, along every endpoint sequence with an interior
limiting slope below `a / (1 + a)`. In particular the slope may be
`a / (1 + 2*a)`; no exact formula for the endpoint or maximizer is assumed.
The domination is uniform in the distance from the moving endpoint. -/
theorem moving_endpoint_sum (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hqa : q < a / (1 + a)) (l : ℕ) (hl : 0 < l) (r : ℕ → ℕ)
    (hr : Tendsto (fun m : ℕ => (r m : ℝ) / m) atTop (𝓝 q)) :
    Tendsto (fun m : ℕ =>
      (∑ i ∈ range (r m + 1), ((m.choose i : ℝ) * a ^ i) ^ l) /
        ((m.choose (r m) : ℝ) * a ^ r m) ^ l)
      atTop (𝓝 ((1 - (q / (a * (1 - q))) ^ l)⁻¹)) := by
  have hq1 : q < 1 := hqa.trans ((div_lt_one (by positivity)).2 (by linarith))
  let ρ : ℝ := q / (a * (1 - q))
  have hρ0 : 0 < ρ := div_pos hq (mul_pos ha (sub_pos.mpr hq1))
  have hρ1 : ρ < 1 := by
    apply (div_lt_one (mul_pos ha (sub_pos.mpr hq1))).2
    have := (lt_div_iff₀ (by positivity : 0 < 1 + a)).mp hqa
    nlinarith
  let w (m i : ℕ) : ℝ := (m.choose i : ℝ) * a ^ i
  let b (m j : ℕ) : ℝ := if j ≤ r m then w m (r m - j) / w m (r m) else 0
  let d (m j : ℕ) : ℝ := ((r m - j : ℕ) : ℝ) /
    (a * ((m - (r m - j) + 1 : ℕ) : ℝ))
  have hw (m i : ℕ) (hi : i ≤ m) : 0 < w m i :=
    mul_pos (by exact_mod_cast Nat.choose_pos hi) (pow_pos ha _)
  have hb0 (m j : ℕ) : 0 ≤ b m j := by
    dsimp [b, w]
    split_ifs <;> positivity
  have hstep (m j : ℕ) (hrm : r m ≤ m) (hj : j + 1 ≤ r m) :
      b m (j + 1) = b m j * d m j := by
    have hjr : j ≤ r m := by omega
    have hs : r m - (j + 1) + 1 = r m - j := by omega
    have hk : r m - (j + 1) ≤ m := by omega
    have hcast : (m.choose (r m - j) : ℝ) * ((r m - j : ℕ) : ℝ) =
        (m.choose (r m - (j + 1)) : ℝ) * ((m - (r m - j) + 1 : ℕ) : ℝ) := by
      have h := Nat.choose_succ_right_eq m (r m - (j + 1))
      rw [hs] at h
      have he : m - (r m - (j + 1)) = m - (r m - j) + 1 := by omega
      rw [he] at h
      exact_mod_cast h
    have hp : a ^ (r m - j) = a ^ (r m - (j + 1)) * a := by
      rw [← hs, pow_succ]
    dsimp [b, d]
    rw [if_pos hj, if_pos hjr]
    dsimp [w]
    have hc : (m.choose (r m) : ℝ) ≠ 0 := (by exact_mod_cast Nat.choose_pos hrm :
      (0 : ℝ) < m.choose (r m)).ne'
    have hd : (((m - (r m - j) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [hp]
    field_simp
    nlinarith [hcast]
  have hd0 (m j : ℕ) : 0 ≤ d m j := by dsimp [d]; positivity
  have hdle (m j : ℕ) : d m j ≤ d m 0 := by
    dsimp [d]
    apply div_le_div₀ (by positivity) (by exact_mod_cast Nat.sub_le (r m) j)
      (by positivity)
    apply mul_le_mul_of_nonneg_left _ ha.le
    exact_mod_cast (show m - r m + 1 ≤ m - (r m - j) + 1 by omega)
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hrR : Tendsto (fun m : ℕ => (r m : ℝ)) atTop atTop := by
    apply (hm.atTop_mul_pos hq hr).congr'
    filter_upwards [eventually_gt_atTop 0] with m hm0
    exact mul_div_cancel₀ _ (by exact_mod_cast hm0.ne' : (m : ℝ) ≠ 0)
  have hrt : Tendsto r atTop atTop := tendsto_natCast_atTop_iff.mp hrR
  have hrle : ∀ᶠ m : ℕ in atTop, r m ≤ m := by
    filter_upwards [hr.eventually (gt_mem_nhds hq1), eventually_gt_atTop 0] with m hm1 hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    exact (by exact_mod_cast (div_lt_one hmR).mp hm1 : r m < m).le
  have hdlim (j : ℕ) : Tendsto (fun m => d m j) atTop (𝓝 ρ) := by
    have hjlim : Tendsto (fun m : ℕ => (j : ℝ) / m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hm
    have h1lim : Tendsto (fun m : ℕ => (1 : ℝ) / m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hm
    have ht := (hr.sub hjlim).div
      (((tendsto_const_nhds.sub hr).add hjlim).add h1lim |>.const_mul a)
      (by simpa using (mul_pos ha (sub_pos.mpr hq1)).ne')
    simp only [sub_zero, add_zero] at ht
    apply ht.congr'
    filter_upwards [hrle, hrt.eventually (eventually_ge_atTop j),
      eventually_gt_atTop 0] with m hrm hj hm0
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
    dsimp [d]
    rw [Nat.cast_sub hj, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (show r m - j ≤ m by omega), Nat.cast_sub hj]
    field_simp
    ring
  have hblim (j : ℕ) : Tendsto (fun m => b m j) atTop (𝓝 (ρ ^ j)) := by
    induction j with
    | zero =>
      simp only [pow_zero]
      apply tendsto_const_nhds.congr'
      filter_upwards [hrle] with m hrm
      simp [b, (hw m (r m) hrm).ne']
    | succ j ih =>
      rw [pow_succ]
      apply (ih.mul (hdlim j)).congr'
      filter_upwards [hrle, hrt.eventually (eventually_ge_atTop (j + 1))] with m hrm hj
      exact (hstep m j hrm hj).symm
  obtain ⟨c, hρc, hc1⟩ := exists_between hρ1
  have hc0 : 0 < c := hρ0.trans hρc
  have hbound : ∀ᶠ m : ℕ in atTop, ∀ j : ℕ, b m j ≤ c ^ j := by
    filter_upwards [hrle, (hdlim 0).eventually (gt_mem_nhds hρc)] with m hrm hdc
    intro j
    induction j with
    | zero => simp [b, (hw m (r m) hrm).ne']
    | succ j ih =>
      by_cases hj : j + 1 ≤ r m
      · rw [hstep m j hrm hj, pow_succ]
        exact mul_le_mul ih ((hdle m j).trans hdc.le) (hd0 m j) (pow_nonneg hc0.le _)
      · simp only [b, if_neg hj]
        positivity
  have hcl : c ^ l < 1 := pow_lt_one₀ hc0.le hc1 (by omega)
  have hρl : ρ ^ l < 1 := pow_lt_one₀ hρ0.le hρ1 (by omega)
  have ht := tendsto_tsum_of_dominated_convergence
    (summable_geometric_of_lt_one (pow_nonneg hc0.le l) hcl)
    (fun j => (hblim j).pow l)
    (hbound.mono fun m hm j => show ‖b m j ^ l‖ ≤ (c ^ l) ^ j by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb0 m j) l), ← pow_mul, mul_comm l j,
        pow_mul]
      exact pow_le_pow_left₀ (hb0 m j) (hm j) l)
  have hsum : (∑' j : ℕ, (ρ ^ j) ^ l) = (1 - ρ ^ l)⁻¹ := by
    simp_rw [← pow_mul, mul_comm _ l, pow_mul]
    exact tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg (pow_nonneg hρ0.le l)]; exact hρl)
  rw [hsum] at ht
  apply ht.congr'
  filter_upwards with m
  have hfinite : (∑' j : ℕ, b m j ^ l) = ∑ j ∈ range (r m + 1), b m j ^ l := by
    apply tsum_eq_sum
    intro j hj
    have hjr : ¬ j ≤ r m := by simpa only [mem_range, Nat.lt_succ_iff] using hj
    simp [b, hjr, Nat.ne_of_gt hl]
  rw [hfinite]
  simp only [b]
  rw [sum_congr rfl (fun j hj => by rw [if_pos (Nat.le_of_lt_succ (mem_range.mp hj)), div_pow])]
  rw [← sum_div]
  congr 1
  simpa only [Nat.add_sub_cancel] using sum_range_reflect (fun i => w m i ^ l) (r m + 1)

end D5.S3.AnalyticClosure.BinomialMovingEndpoint
