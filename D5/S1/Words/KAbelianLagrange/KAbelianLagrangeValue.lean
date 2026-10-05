/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeValue
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeValue
   mirror-E: none(waiver:analytic-value-supplier)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Cauchy]
   utility: none
   digest: Infinite positive digit streams have unique values in all their prefix cylinders. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePrefix
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract Filter
open scoped Topology

/-- Positive simple streams converge to a unique value, which belongs to every closed
prefix cylinder. The digits may be real: integrality is needed later for irrationality,
not for the nested-cylinder construction. -/
theorem positive_stream_value (g : GenContFract ℝ)
    (hg : ∀ i, ∃ a : ℝ, 1 ≤ a ∧ g.s.get? i = some ⟨1, a⟩) :
    ∃! x : ℝ, Tendsto g.convs atTop (𝓝 x) ∧
      ∀ n, x ∈ GenContFract.compExactValue (g.contsAux n) (g.conts n) ''
        Set.Icc (0 : ℝ) 1 := by
  let T (n : ℕ) := GenContFract.compExactValue (g.contsAux n) (g.conts n)
  change ∃! x : ℝ, Tendsto g.convs atTop (𝓝 x) ∧
    ∀ n, x ∈ T n '' Set.Icc (0 : ℝ) 1
  have hform : ∀ n z, T n z =
      (g.nums n + (g.contsAux n).a * z) / (g.dens n + (g.contsAux n).b * z) := by
    intro n z
    by_cases hz : z = 0
    · simp [T, hz, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
        GenContFract.den_eq_conts_b]
    · simp only [T, GenContFract.compExactValue, if_neg hz, GenContFract.nextConts,
        GenContFract.nextNum, GenContFract.nextDen, one_mul,
        GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
      rw [← mul_div_mul_right _ _ hz]
      congr 1 <;> field_simp [hz]
  have hq : ∀ n, 0 < g.dens n := by
    intro n
    have hf : 0 < (Nat.fib (n + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    exact lt_of_lt_of_le hf (prefix_geometry g n (fun i _ => hg i)).1
  have hprev : ∀ n, 0 ≤ (g.contsAux n).b := by
    intro n
    cases n with
    | zero => simp [GenContFract.contsAux]
    | succ n =>
        simpa only [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
          using (hq n).le
  have hden : ∀ n z, 0 ≤ z → 0 < g.dens n + (g.contsAux n).b * z := by
    intro n z hz
    exact add_pos_of_pos_of_nonneg (hq n) (mul_nonneg (hprev n) hz)
  have hstep : ∀ n a z, 1 ≤ a → g.s.get? n = some ⟨1, a⟩ →
      z ∈ Set.Icc (0 : ℝ) 1 →
      T (n + 1) z = T n (1 / (a + z)) := by
    intro n a z ha hs hz
    have haz : 0 < a + z := by linarith [hz.1]
    have ht : 0 ≤ 1 / (a + z) := one_div_nonneg.mpr haz.le
    have hd := hden n (1 / (a + z)) ht
    have hn := hden (n + 1) z hz.1
    rw [hform, hform]
    simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux] at hn hd ⊢
    rw [GenContFract.contsAux_recurrence hs rfl rfl] at hn ⊢
    simp only [one_mul] at hn ⊢
    apply (div_eq_div_iff (ne_of_gt hn) (ne_of_gt hd)).2
    field_simp [ne_of_gt haz]
    ring
  have hfinite : ∀ d n, ∃ z ∈ Set.Icc (0 : ℝ) 1,
      g.convs (n + d) = T n z := by
    intro d
    induction d with
    | zero =>
        intro n
        refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
        rw [hform]
        simp [GenContFract.conv_eq_num_div_den]
    | succ d ih =>
        intro n
        obtain ⟨z, hz, heq⟩ := ih (n + 1)
        obtain ⟨a, ha, hs⟩ := hg n
        have haz : 0 < a + z := by linarith [hz.1]
        refine ⟨1 / (a + z), ⟨(one_div_pos.mpr haz).le, ?_⟩, ?_⟩
        · exact (div_le_one haz).mpr (by linarith [hz.1])
        · rw [show n + (d + 1) = n + 1 + d by omega, heq, hstep n a z ha hs hz]
  have hfinite' : ∀ n m, n ≤ m → g.convs m ∈ T n '' Set.Icc (0 : ℝ) 1 := by
    intro n m hnm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    obtain ⟨z, hz, heq⟩ := hfinite d n
    exact ⟨z, hz, heq.symm⟩
  have hfib : Tendsto (fun n => (Nat.fib (n + 1) : ℝ)) atTop atTop := by
    refine tendsto_atTop.mpr ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop (max N 5)] with n hn
    have hNn : (N : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show N ≤ n + 1 by omega)
    have hnf : ((n + 1 : ℕ) : ℝ) ≤ (Nat.fib (n + 1) : ℝ) := by
      exact_mod_cast Nat.le_fib_self (show 5 ≤ n + 1 by omega)
    exact le_trans hN.le (le_trans hNn hnf)
  have hzero : Tendsto (fun n => 1 / (Nat.fib (n + 1) : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, Pi.inv_apply, zero_pow (by decide : 2 ≠ 0)] using
      hfib.inv_tendsto_atTop.pow 2
  have hcauchy : CauchySeq g.convs := by
    apply cauchySeq_of_le_tendsto_0 (fun n => 1 / (Nat.fib (n + 1) : ℝ) ^ 2)
    · intro m l n hnm hnl
      obtain ⟨z, hz, heqz⟩ := hfinite' n m hnm
      obtain ⟨w, hw, heqw⟩ := hfinite' n l hnl
      rw [Real.dist_eq, ← heqz, ← heqw]
      exact ((prefix_geometry g n (fun i _ => hg i)).2 z hz w hw).2
    · exact hzero
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · intro n
    have hcont : ContinuousOn (T n) (Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn (fun z => T n z) (Set.Icc (0 : ℝ) 1)
      simp_rw [hform]
      apply ContinuousOn.div
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
        (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
      intro z hz
      exact ne_of_gt (hden n z hz.1)
    have hclosed : IsClosed (T n '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn hcont).isClosed
    apply hclosed.mem_of_tendsto hx
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hfinite' n m hm
  · intro y hy
    exact tendsto_nhds_unique hy.1 hx

end D5.S1.Words.KAbelianLagrange
