/- GID: D5/S3/Analytic/Asymptotics/RatioOneLogThreshold
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/RatioOneLogThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic window coverage yields an integer enumeration with adjacent ratios tending to one. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

open Filter
open scoped Topology

namespace RatioOneLogThreshold

/-- If the positive naturals satisfying `q` meet every sufficiently late logarithmic window
`(T, T + h]` for each fixed `h > 0`, their increasing enumeration has adjacent ratios tending
to one. -/
theorem exists_strictMono_ratio_tendsto_one_of_log_windows (q : ℕ → Prop)
    (hwindow : ∀ h : ℝ, 0 < h → ∀ᶠ T : ℝ in atTop,
      ∃ n : ℕ, q n ∧ 0 < n ∧ T < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ T + h) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ k, q (N k)) ∧ (∀ k, 0 < N k) ∧
      Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1) := by
  let p : ℕ → Prop := fun n => q n ∧ 0 < n
  have hinf : (Set.ofPred p).Infinite := by
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hwindow 1 zero_lt_one)
    apply Set.infinite_of_forall_exists_gt
    intro m
    let L := Real.log ((m + 1 : ℕ) : ℝ)
    obtain ⟨n, hqn, hn, hlo, _⟩ := hT₀ (max T₀ L) (le_max_left T₀ L)
    have hm : 0 < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos m)
    have hlog : L < Real.log (n : ℝ) := (le_max_right T₀ L).trans_lt hlo
    have hmn : m + 1 < n :=
      Nat.cast_lt.mp ((Real.log_lt_log_iff hm (Nat.cast_pos.mpr hn)).mp hlog)
    exact ⟨n, ⟨hqn, hn⟩, (Nat.lt_succ_self m).trans hmn⟩
  let N : ℕ → ℕ := Nat.nth p
  have hmono : StrictMono N := Nat.nth_strictMono hinf
  have hmem (k : ℕ) : p (N k) := Nat.nth_mem_of_infinite hinf k
  have hpos (k : ℕ) : 0 < (N k : ℝ) := Nat.cast_pos.mpr (hmem k).2
  have hrange : Set.range N = Set.ofPred p := Nat.range_nth_of_infinite hinf
  have hcastTop : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hmono.tendsto_atTop
  have hlogTop : Tendsto (fun k => Real.log (N k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcastTop
  refine ⟨N, hmono, fun k => (hmem k).1, fun k => (hmem k).2, ?_⟩
  have hgap : Tendsto (fun k => Real.log (N (k + 1) : ℝ) - Real.log (N k : ℝ))
      atTop (𝓝 0) := by
    refine tendsto_order.mpr ⟨?_, ?_⟩
    · intro a ha
      refine Eventually.of_forall fun k => ?_
      have hnext : (N k : ℝ) ≤ (N (k + 1) : ℝ) :=
        Nat.cast_le.mpr (hmono.monotone (Nat.le_succ k))
      exact ha.trans_le (sub_nonneg.mpr (Real.log_le_log (hpos k) hnext))
    · intro b hb
      refine (hlogTop.eventually (hwindow (b / 2) (half_pos hb))).mono ?_
      intro k hk
      obtain ⟨n, hqn, hn, hlo, hhi⟩ := hk
      -- The strict lower endpoint places the witness after index `k`.
      have hn_mem : n ∈ Set.ofPred p := ⟨hqn, hn⟩
      rw [← hrange] at hn_mem
      obtain ⟨j, rfl⟩ := hn_mem
      have hlt : N k < N j :=
        Nat.cast_lt.mp ((Real.log_lt_log_iff (hpos k) (hpos j)).mp hlo)
      have hkj : k < j := hmono.lt_iff_lt.mp hlt
      have hnext : N (k + 1) ≤ N j := hmono.monotone (Nat.succ_le_of_lt hkj)
      have hlog_le : Real.log (N (k + 1) : ℝ) ≤ Real.log (N j : ℝ) :=
        Real.log_le_log (hpos (k + 1)) (Nat.cast_le.mpr hnext)
      have hgap_le : Real.log (N (k + 1) : ℝ) - Real.log (N k : ℝ) ≤ b / 2 :=
        sub_le_iff_le_add'.mpr (hlog_le.trans hhi)
      exact hgap_le.trans_lt (half_lt_self hb)
  refine (Real.tendsto_exp_nhds_zero_nhds_one.comp hgap).congr fun k => ?_
  change Real.exp (Real.log (N (k + 1) : ℝ) - Real.log (N k : ℝ)) =
    (N (k + 1) : ℝ) / (N k : ℝ)
  rw [Real.exp_sub, Real.exp_log (hpos (k + 1)), Real.exp_log (hpos k)]

end RatioOneLogThreshold
