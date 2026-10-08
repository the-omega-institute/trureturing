/- GID: D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualGlobalConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive selected jumps bound the actual Cloitre limsup and characterize convergence. -/

import D5.S1.Recurrence.Invariants.CloitreActualRightProfile
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Data.Nat.Fib.Zeckendorf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.CloitreActualGlobalConvergence

open Filter Topology
open D5.S1.Recurrence.Invariants.CloitreActualRightProfile

local notation "F" => Nat.fib
local notation "Q" => Nat.greatestFib
local notation "α" => Real.goldenRatio⁻¹
local notation "R" => (fun n : ℕ => (C n : ℝ) / n)
local notation "J" => (fun n : ℕ =>
  max ((g n : ℝ) - (T n (g n) : ℝ)) 0 / n)

/-- Position in the half-open Fibonacci analysis block. -/
noncomputable def position (n : ℕ) : ℝ :=
  ((n : ℝ) - F (Q n)) / F (Q n - 1)

private theorem block_facts (n : ℕ) (hn : 8 ≤ n) :
    6 ≤ Q n ∧ F (Q n) ≤ n ∧ n < F (Q n + 1) ∧
    F (Q n) = F (Q n - 1) + F (Q n - 2) ∧
    F (Q n + 1) = 2 * F (Q n - 1) + F (Q n - 2) := by
  have hq : 6 ≤ Q n := Nat.le_greatestFib.mpr (by exact (show F 6 = 8 by decide) ▸ hn)
  have hs := Nat.fib_add_two (n := Q n - 2)
  have ht := Nat.fib_add_two (n := Q n - 1)
  rw [show Q n - 2 + 2 = Q n by omega,
    show Q n - 2 + 1 = Q n - 1 by omega] at hs
  rw [show Q n - 1 + 2 = Q n + 1 by omega,
    show Q n - 1 + 1 = Q n by omega] at ht
  exact ⟨hq, Nat.fib_greatestFib_le n, Nat.lt_fib_greatestFib_add_one n,
    by omega, by omega⟩

private theorem position_mem (n : ℕ) (hn : 8 ≤ n) : position n ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hq, hlo, hhi, hs, ht⟩ := block_facts n hn
  have hp : 0 < F (Q n - 1) := Nat.fib_pos.mpr (by omega)
  have hp' : (0 : ℝ) < F (Q n - 1) := by exact_mod_cast hp
  have hlo' : (F (Q n) : ℝ) ≤ n := by exact_mod_cast hlo
  have hhi' : (n : ℝ) < F (Q n + 1) := by exact_mod_cast hhi
  have hs' := congrArg (fun k : ℕ => (k : ℝ)) hs
  have ht' := congrArg (fun k : ℕ => (k : ℝ)) ht
  push_cast at hs' ht'
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo') hp'.le
  · apply (div_le_iff₀ hp').mpr
    linarith

private theorem child_bounds (U : ℕ → ℕ) (h : Hyp21_1 U) (n : ℕ) (hn : 8 ≤ n) :
    n ≤ 5 * g n ∧ n ≤ 5 * (n - g n) ∧ 1 ≤ g n ∧ g n < n := by
  obtain ⟨hq, hlo, hhi, hs, ht⟩ := block_facts n hn
  have hd := actual_foundations.1 n (d n) (by omega)
  change 1 ≤ g n ∧ g n ≤ n - 1 at hd
  have hc := h.cyclesInside (Q n) (n - F (Q n)) (g n) hq
    (by simpa only [Nat.add_sub_of_le hlo, D, Set.mem_Icc] using hd)
    (by simpa [Nat.add_sub_of_le hlo] using selected_periodic U h n (by omega))
  change F (Q n - 1) ≤ g n ∧ g n ≤ F (Q n - 1) + (n - F (Q n)) at hc
  have hm := Nat.fib_mono (show Q n - 2 ≤ Q n - 1 by omega)
  have hb := Nat.fib_add_two (n := Q n - 3)
  rw [show Q n - 3 + 2 = Q n - 1 by omega,
    show Q n - 3 + 1 = Q n - 2 by omega] at hb
  have hm' := Nat.fib_mono (show Q n - 3 ≤ Q n - 2 by omega)
  constructor
  · omega
  · constructor
    · omega
    · exact ⟨hd.1, by omega⟩

private theorem index_tendsto : Tendsto Q atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro k
  filter_upwards [eventually_ge_atTop (F k)] with n hn
  exact Nat.le_greatestFib.mpr hn

private theorem child_tendsto (U : ℕ → ℕ) (h : Hyp21_1 U) :
    Tendsto g atTop atTop ∧ Tendsto (fun n => n - g n) atTop atTop := by
  constructor <;> refine tendsto_atTop.2 (fun k => ?_)
  · filter_upwards [eventually_ge_atTop (max 8 (5 * k))] with n hn
    have hb := child_bounds U h n (by omega)
    omega
  · filter_upwards [eventually_ge_atTop (max 8 (5 * k))] with n hn
    have hb := child_bounds U h n (by omega)
    omega

private theorem ratio_bounds (U : ℕ → ℕ) (h : Hyp21_1 U) :
    ∀ᶠ n in atTop, 0 ≤ R n ∧ R n ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hb := h.bounds n hn
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,
    (div_le_one hp).mpr (by exact_mod_cast (hb.2.2.1.trans hb.2.2.2))⟩

private theorem jump_nonneg (n : ℕ) : 0 ≤ J n :=
  div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)

private theorem jump_le (n : ℕ) (hn : 3 ≤ n) : J n ≤ 1 := by
  have hd := actual_foundations.1 n (d n) hn
  change 1 ≤ g n ∧ g n ≤ n - 1 at hd
  have hg : (g n : ℝ) ≤ n := by exact_mod_cast (show g n ≤ n by omega)
  have ht : (0 : ℝ) ≤ T n (g n) := Nat.cast_nonneg _
  have np : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (div_le_one np).mpr
  exact max_le (by linarith) (Nat.cast_nonneg _)

private theorem adjacent_ratio (k : ℕ) :
    Tendsto (fun n => (F (Q n - k + 1) : ℝ) / F (Q n - k))
      atTop (nhds Real.goldenRatio) :=
  tendsto_fib_succ_div_fib_atTop.comp ((tendsto_sub_atTop_nat k).comp index_tendsto)

private theorem global_upper (U : ℕ → ℕ) (h : Hyp21_1 U) :
    limsup R atTop ≤ α + Real.goldenRatio * limsup J atTop := by
  classical
  let b := limsup R atTop
  let k := limsup J atTop
  have rb := ratio_bounds U h
  have rbd : IsBoundedUnder (· ≤ ·) atTop R :=
    isBoundedUnder_of_eventually_le (rb.mono fun _ hn => hn.2)
  have rc : IsCoboundedUnder (· ≤ ·) atTop R :=
    (isBoundedUnder_of_eventually_ge (rb.mono fun _ hn => hn.1)).isCoboundedUnder_le
  have jbd : IsBoundedUnder (· ≤ ·) atTop J :=
    isBoundedUnder_of_eventually_le ((eventually_ge_atTop 3).mono jump_le)
  have jc : IsCoboundedUnder (· ≤ ·) atTop J :=
    isCoboundedUnder_le_of_le atTop jump_nonneg
  have knon : 0 ≤ k := le_limsup_of_le jbd (fun a ha =>
    le_of_tendsto tendsto_const_nhds ((ha.and (Eventually.of_forall
      jump_nonneg)).mono fun _ hn => hn.2.trans hn.1))
  by_contra! hbad
  change α + Real.goldenRatio * k < b at hbad
  have ba : α < b := lt_of_le_of_lt
    (le_add_of_nonneg_right (mul_nonneg Real.goldenRatio_pos.le knon)) hbad
  have bp : 0 < 1 + b := by linarith [inv_pos.mpr Real.goldenRatio_pos]
  let H : Set ℝ := {t | MapClusterPt (b, t) atTop (fun n => (R n, position n))}
  have Hclosed : IsClosed H :=
    isClosed_setOfPred_clusterPt.preimage (continuous_const.prodMk continuous_id)
  have Hsub : H ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    have hc : MapClusterPt t atTop position :=
      ht.continuousAt_comp continuous_snd.continuousAt
    exact isClosed_Icc.mem_of_mapClusterPt hc
      ((eventually_ge_atTop 8).mono fun n hn => position_mem n hn)
  have Hcompact : IsCompact H := isCompact_Icc.of_isClosed_subset Hclosed Hsub
  have Hne : H.Nonempty := by
    obtain ⟨u, hu, hut⟩ := exists_seq_tendsto_limsup rc rbd
    obtain ⟨t, ht, v, hv, hvlim⟩ := isCompact_Icc.tendsto_subseq'
      (((hut.eventually (eventually_ge_atTop 8)).mono
        (fun i hi => position_mem (u i) hi)).frequently)
    refine ⟨t, ?_⟩
    exact ((hu.comp hv.tendsto_atTop).prodMk_nhds hvlim).mapClusterPt.of_comp
      (hut.comp hv.tendsto_atTop)
  obtain ⟨t, ht, hmin⟩ := Hcompact.exists_isMinOn Hne continuous_id.continuousOn
  obtain ⟨u, hu, hut⟩ := ht.exists_seq_tendsto
  have hur : Tendsto (fun i => R (u i)) atTop (nhds b) := (continuous_fst.tendsto (b, t)).comp hu
  have hup : Tendsto (fun i => position (u i)) atTop (nhds t) := (continuous_snd.tendsto (b, t)).comp hu
  let zseq := fun i => ((g (u i) : ℝ) / u i, R (g (u i)), R (u i - g (u i)))
  have zmem : ∀ᶠ i in atTop, zseq i ∈ Set.Icc ((0 : ℝ), (0 : ℝ), (0 : ℝ)) (1, 1, 1) := by
    filter_upwards [hut.eventually (eventually_ge_atTop 8),
      ((child_tendsto U h).1.comp hut).eventually rb,
      ((child_tendsto U h).2.comp hut).eventually rb] with i hi hg hh
    have hb := child_bounds U h (u i) hi
    have un : (0 : ℝ) < u i := by exact_mod_cast (show 0 < u i by omega)
    have gu : (g (u i) : ℝ) ≤ u i := by exact_mod_cast hb.2.2.2.le
    exact ⟨⟨div_nonneg (Nat.cast_nonneg _) un.le, hg.1, hh.1⟩,
      (div_le_one un).mpr gu, hg.2, hh.2⟩
  obtain ⟨z, hz, v, hv, hzlim⟩ := isCompact_Icc.tendsto_subseq' zmem.frequently
  let n := u ∘ v
  have nt : Tendsto n atTop atTop := hut.comp hv.tendsto_atTop
  have nr : Tendsto (fun i => R (n i)) atTop (nhds b) := hur.comp hv.tendsto_atTop
  have np : Tendsto (fun i => position (n i)) atTop (nhds t) := hup.comp hv.tendsto_atTop
  have wa : Tendsto (fun i => (g (n i) : ℝ) / n i) atTop (nhds z.1) := (continuous_fst.tendsto z).comp hzlim
  have xr : Tendsto (fun i => R (g (n i))) atTop (nhds z.2.1) := (continuous_fst.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim)
  have yr : Tendsto (fun i => R (n i - g (n i))) atTop (nhds z.2.2) := (continuous_snd.tendsto z.2).comp ((continuous_snd.tendsto z).comp hzlim)
  have aBounds : (1 / 5 : ℝ) ≤ z.1 ∧ z.1 ≤ 4 / 5 := by
    constructor
    · apply ge_of_tendsto wa
      filter_upwards [nt.eventually (eventually_ge_atTop 8)] with i hi
      have hb := child_bounds U h (n i) hi
      have un : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
      apply (le_div_iff₀ un).mpr
      have hb' : (n i : ℝ) ≤ 5 * g (n i) := by exact_mod_cast hb.1
      linarith only [hb']
    · apply le_of_tendsto wa
      
      filter_upwards [nt.eventually (eventually_ge_atTop 8)] with i hi
      have hb := child_bounds U h (n i) hi
      have un : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
      apply (div_le_iff₀ un).mpr
      have hb' : (n i : ℝ) ≤ 5 * ((n i : ℝ) - g (n i)) := by
        have cast : (n i : ℝ) ≤ 5 * (n i - g (n i) : ℕ) := by exact_mod_cast hb.2.1
        simpa only [Nat.cast_sub hb.2.2.2.le] using cast
      linarith only [hb']
  have xb : z.2.1 ≤ b := by
    apply le_of_forall_pos_le_add
    intro e he
    apply le_of_tendsto xr
    exact ((child_tendsto U h).1.comp nt).eventually
      ((eventually_lt_of_limsup_lt (show b < b + e by linarith) rbd).mono
        fun _ hn => hn.le)
  have yb : z.2.2 ≤ b := by
    apply le_of_forall_pos_le_add
    intro e he
    apply le_of_tendsto yr
    exact ((child_tendsto U h).2.comp nt).eventually
      ((eventually_lt_of_limsup_lt (show b < b + e by linarith) rbd).mono
        fun _ hn => hn.le)
  have avg : b = z.1 * z.2.1 + (1 - z.1) * z.2.2 := by
    apply tendsto_nhds_unique nr
    apply ((wa.mul xr).add ((tendsto_const_nhds.sub wa).mul yr)).congr'
    filter_upwards [nt.eventually (eventually_ge_atTop 8)] with i hi
    have hb := child_bounds U h (n i) hi
    have un : (n i : ℝ) ≠ 0 := by exact_mod_cast (show n i ≠ 0 by omega)
    have gn : (g (n i) : ℝ) ≠ 0 := by exact_mod_cast (show g (n i) ≠ 0 by omega)
    have hn : ((n i - g (n i) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show n i - g (n i) ≠ 0 by omega)
    have split :=  congrArg (fun k : ℕ => (k : ℝ))
      (actual_foundations.2 (n i) (by omega))
    push_cast at split
    rw [show 1 - (g (n i) : ℝ) / n i = (n i - g (n i) : ℕ) / (n i : ℝ) by
      rw [Nat.cast_sub hb.2.2.2.le]
      field_simp [un]
      <;> ring]
    rw [div_mul_div_cancel₀' gn, div_mul_div_cancel₀' hn, ← add_div, ← split]
  have xe : z.2.1 = b := by
    have hprod := mul_nonneg (sub_nonneg.mpr (show z.1 ≤ 1 by linarith [aBounds.2]))
      (sub_nonneg.mpr yb)
    nlinarith [aBounds.1]
  have xgold : Tendsto (fun i => R (g (n i))) atTop (nhds b) := by simpa [xe] using xr
  have jump : z.1 * (1 + b) ≤ 1 + k := by
    apply le_of_forall_pos_le_add
    intro e he
    have jl := nt.eventually (eventually_lt_of_limsup_lt
      (show k < k + e by linarith) jbd)
    apply le_of_tendsto (wa.mul (tendsto_const_nhds.add xgold))
    filter_upwards [jl, nt.eventually (eventually_ge_atTop 8)] with i hi hn
    have hb := child_bounds U h (n i) hn
    have hgC := (h.bounds (g (n i)) hb.2.2.1).2.2.1.trans
      ((h.bounds (g (n i)) hb.2.2.1).2.2.2)
    have hp : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
    have gn : (g (n i) : ℝ) ≠ 0 := by exact_mod_cast (show g (n i) ≠ 0 by omega)
    have tc : (T (n i) (g (n i)) : ℝ) = (n i : ℝ) - C (g (n i)) := by
      unfold T
      rw [Nat.cast_sub (hgC.trans hb.2.2.2.le)]
    have km := le_max_left ((g (n i) : ℝ) - T (n i) (g (n i))) 0
    have kk : ((g (n i) : ℝ) - T (n i) (g (n i))) / n i ≤ J (n i) :=
      div_le_div_of_nonneg_right km hp.le
    have ident : (g (n i) : ℝ) / n i * (1 + R (g (n i))) =
        1 + ((g (n i) : ℝ) - T (n i) (g (n i))) / n i := by
      rw [tc]
      field_simp
      ring
    rw [ident]
    linarith
  have ap : z.1 < α := by
    have cancel : α * Real.goldenRatio = 1 := inv_mul_cancel₀ Real.goldenRatio_ne_zero
    have sq : α * (1 + α) = 1 := by
      have ha : 1 + α = Real.goldenRatio := by
        rw [Real.inv_goldenRatio]
        linarith [Real.goldenRatio_add_goldenConj]
      rwa [ha]
    have kb : 1 + k < α * (1 + b) := by
      nlinarith [mul_pos (inv_pos.mpr Real.goldenRatio_pos)
        (sub_pos.mpr hbad)]
    nlinarith
  -- A strict selector weight puts the selected child in the preceding analysis block.
  have phi : Tendsto (fun i => (F (Q (n i) + 1) : ℝ) / F (Q (n i)))
      atTop (nhds Real.goldenRatio) := (adjacent_ratio 0).comp nt
  have apl : z.1 * Real.goldenRatio < 1 := by
    have cc := inv_mul_cancel₀ Real.goldenRatio_ne_zero
    have := mul_lt_mul_of_pos_right ap Real.goldenRatio_pos
    simpa only [cc] using this
  have childBlock : ∀ᶠ i in atTop, Q (g (n i)) = Q (n i) - 1 := by
    have lowprod := (wa.mul phi).eventually (gt_mem_nhds apl)
    filter_upwards [lowprod, nt.eventually (eventually_ge_atTop 8)] with i hi hn
    obtain ⟨hq, hlo, hhi, hs, ht'⟩ := block_facts (n i) hn
    have hb := child_bounds U h (n i) hn
    have hc := h.cyclesInside (Q (n i)) (n i - F (Q (n i))) (g (n i)) hq
      (by simpa only [Nat.add_sub_of_le hlo, g] using actual_foundations.1 (n i) (d (n i)) (by omega))
      (by simpa [Nat.add_sub_of_le hlo] using selected_periodic U h (n i) (by omega))
    have un : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
    have fn : (0 : ℝ) < F (Q (n i)) := by
      exact_mod_cast (Nat.fib_pos.mpr (show 0 < Q (n i) by omega))
    have gh : (g (n i) : ℝ) < F (Q (n i)) := by
      have hi' := (div_lt_iff₀ (mul_pos un fn)).mp
        (show (g (n i) : ℝ) * F (Q (n i) + 1) / ((n i : ℝ) * F (Q (n i))) < 1 by
          simpa only [div_mul_div_comm] using hi)
      have nh : (n i : ℝ) < F (Q (n i) + 1) := by exact_mod_cast hhi
      have gp : (0 : ℝ) < g (n i) := by exact_mod_cast (show 0 < g (n i) by omega)
      nlinarith
    have upper : Q (g (n i)) < Q (n i) := Nat.greatestFib_lt.mpr (by exact_mod_cast gh)
    have lower : Q (n i) - 1 ≤ Q (g (n i)) := Nat.le_greatestFib.mpr hc.1
    omega
  have fib1 : Tendsto (fun i => (F (Q (n i) - 1) : ℝ) / F (Q (n i) - 2))
      atTop (nhds Real.goldenRatio) := by
    apply ((adjacent_ratio 2).comp nt).congr'
    filter_upwards [nt.eventually (eventually_ge_atTop 8)] with i hi
    dsimp only [Function.comp_def]
    rw [show Q (n i) - 2 + 1 = Q (n i) - 1 by have := (block_facts (n i) hi).1; omega]
  have fib2 : Tendsto (fun i => (F (Q (n i)) : ℝ) / F (Q (n i) - 1))
      atTop (nhds Real.goldenRatio) := by
    apply ((adjacent_ratio 1).comp nt).congr'
    filter_upwards [nt.eventually (eventually_ge_atTop 8)] with i hi
    dsimp only [Function.comp_def]
    rw [show Q (n i) - 1 + 1 = Q (n i) by have := (block_facts (n i) hi).1; omega]
  have descent : Tendsto (fun i => position (g (n i))) atTop
      (nhds (z.1 * (Real.goldenRatio ^ 2 + t * Real.goldenRatio) - Real.goldenRatio)) := by
    simp only [pow_two]
    apply ((wa.mul ((fib2.mul fib1).add (np.mul fib1))).sub fib1).congr'
    filter_upwards [childBlock, nt.eventually (eventually_ge_atTop 8)] with i hi hn
    have hq := (block_facts (n i) hn).1
    have f1 : (F (Q (n i) - 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.fib_pos.mpr (show 0 < Q (n i) - 1 by omega)).ne'
    have f2 : (F (Q (n i) - 2) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.fib_pos.mpr (show 0 < Q (n i) - 2 by omega)).ne'
    have un : (n i : ℝ) ≠ 0 := by exact_mod_cast (show n i ≠ 0 by omega)
    unfold position
    rw [hi, show Q (n i) - 1 - 1 = Q (n i) - 2 by omega]
    field_simp
    ring
  have below : z.1 * (Real.goldenRatio ^ 2 + t * Real.goldenRatio) - Real.goldenRatio < t := by
    have tnon := (Hsub ht).1
    have ha : α * Real.goldenRatio = 1 := inv_mul_cancel₀ Real.goldenRatio_ne_zero
    have hh := mul_pos (sub_pos.mpr ap)
      (show 0 < Real.goldenRatio ^ 2 + t * Real.goldenRatio by positivity)
    nlinarith [Real.goldenRatio_sq]
  have hnew : z.1 * (Real.goldenRatio ^ 2 + t * Real.goldenRatio) - Real.goldenRatio ∈ H :=
    (xgold.prodMk_nhds descent).mapClusterPt.of_comp ((child_tendsto U h).1.comp nt)
  have minle := hmin hnew
  exact (not_lt_of_ge minle) below

private theorem cycle_control {w : ℕ → ℝ} {p : ℕ} {q e : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1)
    (hm : ∀ i, w (i % p) = w i)
    (hs : ∀ i, w (i + 1) ≤ q * w i + e) :
    ∀ i, w i ≤ e / (1 - q) := by
  obtain ⟨j, hj, hmax⟩ := (Finset.range p).exists_max_image w
    ⟨0, Finset.mem_range.mpr hp⟩
  have allmax : ∀ i, w i ≤ w j := by
    intro i
    rw [← hm i]
    exact hmax (i % p) (Finset.mem_range.mpr (Nat.mod_lt i hp))
  have period : w (j + p) = w j := by
    rw [← hm (j + p), Nat.add_mod_right, hm j]
  have hh := hs (j + p - 1)
  rw [show j + p - 1 + 1 = j + p by omega, period] at hh
  have hc := mul_le_mul_of_nonneg_left (allmax (j + p - 1)) hq
  have maxbound : w j ≤ e / (1 - q) := (le_div_iff₀ (sub_pos.mpr hq1)).mpr (by nlinarith)
  exact fun i => (allmax i).trans maxbound

private theorem convergence_implies_jumps (U : ℕ → ℕ) (h : Hyp21_1 U)
    (hr : Tendsto R atTop (nhds α)) : Tendsto J atTop (nhds 0) := by
  let a : ℝ := α
  have a0 : 0 < a := inv_pos.mpr Real.goldenRatio_pos
  have a1 : a < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have asq : a * a = 1 - a := by
    have ha : 1 + a = Real.goldenRatio := by
      dsimp only [a]
      rw [Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    have hc : a * Real.goldenRatio = 1 := inv_mul_cancel₀ Real.goldenRatio_ne_zero
    nlinarith
  change Tendsto R atTop (nhds a) at hr
  clear_value a
  apply Metric.tendsto_atTop.2
  intro e he
  let δ := e * (1 - a) / 4
  have dp : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hr δ dp
  refine ⟨max 8 (3 * M), ?_⟩
  intro n hn
  obtain ⟨hq, hlo, hhi, hs, ht⟩ := block_facts n (by omega)
  have hgD := actual_foundations.1 n (d n) (by omega)
  change g n ∈ D n at hgD
  have hgp := selected_periodic U h n (by omega)
  have hgI : g n ∈ I (Q n) (n - F (Q n)) :=
    h.cyclesInside (Q n) (n - F (Q n)) (g n) hq
      (by simpa only [Nat.add_sub_of_le hlo] using hgD)
      (by simpa only [Nat.add_sub_of_le hlo] using hgp)
  have inv : Set.MapsTo (T n) (I (Q n) (n - F (Q n)))
      (I (Q n) (n - F (Q n))) := by
    simpa only [Nat.add_sub_of_le hlo] using h.collarInvariant (Q n) (n - F (Q n)) hq
  have collar : ∀ i, (T n)^[i] (g n) ∈ I (Q n) (n - F (Q n)) :=
    fun i => inv.iterate i hgI
  have legal : ∀ i, (T n)^[i] (g n) ∈ D n := by
    intro i
    have hc := h.collarDomain (Q n) (n - F (Q n)) hq (collar i)
    simpa only [Nat.add_sub_of_le hlo] using hc
  have low : ∀ i, M ≤ (T n)^[i] (g n) := by
    intro i
    have hf := Nat.fib_mono (show Q n - 2 ≤ Q n - 1 by omega)
    have hc := (collar i).1
    omega
  obtain ⟨p, hp, hperiod⟩ := hgp
  let x := fun i => (T n)^[i] (g n)
  let w := fun i => |(x i : ℝ) / n - a|
  have np : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have step : ∀ i, w (i + 1) ≤ a * w i + δ := by
    intro i
    have hx := legal i
    change 1 ≤ x i ∧ x i ≤ n - 1 at hx
    have xp : (0 : ℝ) < x i := by exact_mod_cast (show 0 < x i by omega)
    have ynon : 0 ≤ (x i : ℝ) / n := div_nonneg xp.le np.le
    have yle : (x i : ℝ) / n ≤ 1 := (div_le_one np).mpr (by exact_mod_cast (show x i ≤ n by omega))
    have err := hM (x i) (low i)
    rw [Real.dist_eq] at err
    have cLe : C (x i) ≤ n :=
      ((h.bounds (x i) hx.1).2.2.1.trans (h.bounds (x i) hx.1).2.2.2).trans (by omega)
    have eqstep : (x (i + 1) : ℝ) / n - a =
        -a * ((x i : ℝ) / n - a) - (R (x i) - a) * ((x i : ℝ) / n) := by
      have xs : x (i + 1) = T n (x i) := Function.iterate_succ_apply' (T n) i (g n)
      rw [xs, T, Nat.cast_sub cLe]
      field_simp [np.ne', xp.ne']
      linear_combination -(n : ℝ) * asq
    dsimp [w]
    rw [eqstep]
    calc
      |-a * ((x i : ℝ) / n - a) - (R (x i) - a) * ((x i : ℝ) / n)|
          ≤ |-a * ((x i : ℝ) / n - a)| + |(R (x i) - a) * ((x i : ℝ) / n)| := abs_sub _ _
      _ = a * |(x i : ℝ) / n - a| + |R (x i) - a| * ((x i : ℝ) / n) := by
        rw [abs_mul, abs_neg, abs_of_pos a0, abs_mul, abs_of_nonneg ynon]
      _ ≤ a * |(x i : ℝ) / n - a| + δ := by
        have hh := mul_le_mul_of_nonneg_left yle (abs_nonneg (R (x i) - a))
        nlinarith
  have control : ∀ i, w i ≤ δ / (1 - a) := cycle_control hp a0.le a1
    (fun i => by dsimp [w, x]; rw [hperiod.iterate_mod_apply]) step
  have jbound : J n ≤ 2 * (δ / (1 - a)) := by
    have w0 := control 0
    have w1 := control 1
    change |(g n : ℝ) / n - a| ≤ δ / (1 - a) at w0
    change |(T n (g n) : ℝ) / n - a| ≤ δ / (1 - a) at w1
    have hh := abs_sub ((g n : ℝ) / n - a) ((T n (g n) : ℝ) / n - a)
    have gap : ((g n : ℝ) - T n (g n)) / n ≤ 2 * (δ / (1 - a)) := by
      have ha := le_abs_self ((g n : ℝ) / n - (T n (g n) : ℝ) / n)
      rw [sub_sub_sub_cancel_right] at hh
      rw [sub_div]
      linarith
    apply (div_le_iff₀ np).mpr
    apply max_le
    · exact (div_le_iff₀ np).mp gap
    · positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (jump_nonneg n)]
  have simplify : 2 * (δ / (1 - a)) = e / 2 := by
    dsimp only [δ]
    field_simp [(sub_pos.mpr a1).ne']
    <;> ring
  rw [simplify] at jbound
  linarith

/-- The selected positive-jump rate bounds the global limsup, and vanishes
exactly when the actual value ratio converges to the inverse golden ratio. -/
theorem result (U : ℕ → ℕ) (h : Hyp21_1 U) :
    limsup R atTop ≤ α + Real.goldenRatio * limsup J atTop ∧
    (Tendsto R atTop (nhds α) ↔ Tendsto J atTop (nhds 0)) := by
  have upper := global_upper U h
  refine ⟨upper, convergence_implies_jumps U h, ?_⟩
  intro hj
  have a0 : 0 < α := inv_pos.mpr Real.goldenRatio_pos
  have rb := ratio_bounds U h
  have rbd := isBoundedUnder_of_eventually_le (rb.mono fun _ hn => hn.2)
  have rlower := isBoundedUnder_of_eventually_ge (rb.mono fun _ hn => hn.1)
  have lower : α ≤ liminf R atTop := by
    let G := D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
    have glimit : Tendsto (fun n => (G n : ℝ) / n) atTop (nhds α) := by
      have natlim : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      have fl := (tendsto_nat_floor_mul_div_atTop a0.le).comp natlim
      have scale : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (nhds 1) := by
        have invn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        apply (show Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (nhds 1) by
          simpa only [add_zero] using (tendsto_const_nhds.add invn)).congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have nn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        simp only [add_div, div_self nn, one_div]
      apply (show Tendsto (fun n : ℕ => ((⌊α * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1)) *
          (((n : ℝ) + 1) / n)) atTop (nhds α) by
        simpa only [mul_one, Function.comp_def] using fl.mul scale).congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      dsimp only [G, D5.S1.Phase.SelfReference.GoldenShellRecurrence.g]
      rw [mul_comm α]
      exact div_mul_div_cancel₀ (show (n : ℝ) + 1 ≠ 0 by positivity)
    have gb : IsBoundedUnder (· ≥ ·) atTop (fun n => (G n : ℝ) / n) :=
      isBoundedUnder_of ⟨0, fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
    rw [← glimit.liminf_eq]
    apply liminf_le_liminf (hu := gb) (hv := rbd.isCoboundedUnder_ge)
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (h.bounds n hn).2.1
  have sup : limsup R atTop ≤ α := by simpa [hj.limsup_eq] using upper
  exact tendsto_of_le_liminf_of_limsup_le lower sup rbd rlower

end D5.S1.Recurrence.Invariants.CloitreActualGlobalConvergence

