/- GID: D5/S1/Recurrence/KatzCutoff/Result
   generality: I
   mirror-B: D5/B/S1/Recurrence/KatzCutoff/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Path Katz cut-off values converge to one over the square root of five. -/

/-
admission_basis: open-problem-resolution (#20122; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_monotoneOn
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20795
t: proof_shape: bind-only; escape_witness: none; consumers: RAB_t, R_limit, t_bounds.
t_bounds: proof_shape: bind-only; escape_witness: none; consumers: RAB_t, R_limit.
RAB_t: proof_shape: bind-only; escape_witness: none; consumers: R_limit.
aa_tendsto: proof_shape: bind-only; escape_witness: none; consumers: R_limit.
bb_tendsto: proof_shape: bind-only; escape_witness: none; consumers: R_limit.
R_limit: proof_shape: bind-only; escape_witness: none; consumers: R_eventually_gt_one.
beta_limit_gt_one: proof_shape: bind-only; escape_witness: none; consumers: R_eventually_gt_one.
R_eventually_gt_one: proof_shape: bind-only; escape_witness: none; consumers: result.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
root_above_and_tendsto: proof_shape: bind-only; escape_witness: none; consumers: result.
crossing_exists_unique: proof_shape: bind-only; escape_witness: none; consumers: R_crossing.
continuous_d: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Result.continuous_d; consumers: R_continuousOn.
d_pos_le_half: proof_shape: bind-only; escape_witness: none; consumers: R_continuousOn.
R_continuousOn: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Result.continuous_d; consumers: R_crossing.
p1_zero_iff: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.ProductExtrema.wronskian; consumers: result.
R_crossing: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_monotoneOn; consumers: R_root_exists.
R_root_exists: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_monotoneOn; consumers: result.
result: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_monotoneOn; consumers: settling result.
-/

import D5.S1.Recurrence.KatzCutoff.ProductExtrema
import D5.S1.Recurrence.KatzCutoff.Reduction
import D5.S1.Recurrence.KatzCutoff.Monotone

set_option maxHeartbeats 1000000

namespace D5.S1.Recurrence.KatzCutoff.Result

open Matrix Finset Filter Topology
open D5.S1.Recurrence.KatzCutoff.ProductExtrema
open D5.S1.Recurrence.KatzCutoff.Reduction
open D5.S1.Recurrence.KatzCutoff.Monotone

private noncomputable def t (α : ℝ) : ℝ := rm α/rp α

private lemma t_bounds {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) : 0 < t α ∧ t α < 1 := by
  have hs := s_pos hα hα'
  have hsq := s_sq hα hα'
  have hs1 : (Real.sqrt (1 - 4*α^2)) < 1 := by nlinarith
  have hm : 0 < rm α := by dsimp [rm]; linarith
  constructor
  · exact div_pos hm (rp_pos hα hα')
  · apply (div_lt_one (rp_pos hα hα')).2
    dsimp [rp,rm]
    linarith

private lemma RAB_t {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    RAB α a b = (α/(Real.sqrt (1 - 4*α^2)))*((1-t α^a)*(1-t α^b))/(1-t α^(a+b)) := by
  have hp := ne_of_gt (rp_pos hα hα')
  have ht := t_bounds hα hα'
  have hden : 1-t α^(a+b) ≠ 0 := by
    have hx := pow_lt_one₀ ht.1.le ht.2 (by omega : a+b ≠ 0)
    linarith
  have hfac (k : ℕ) : rp α^k-rm α^k = rp α^k*(1-t α^k) := by
    dsimp [t]
    rw [div_pow]
    field_simp
  rw [RAB_closed hα hα' ha hb,hfac a,hfac b,hfac (a+b),pow_add]
  field_simp [hp,hden]

private lemma aa_tendsto : Tendsto (fun n : ℕ => n/2) atTop atTop := by
  exact Nat.tendsto_div_const_atTop (by decide : 2 ≠ 0)

private lemma bb_tendsto : Tendsto (fun n : ℕ => (n-1)/2) atTop atTop := by
  exact (Nat.tendsto_div_const_atTop (by decide : 2 ≠ 0)).comp (tendsto_sub_atTop_nat 1)

private lemma R_limit {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) :
    Tendsto (fun n => RAB α ((n/2)) (((n-1)/2))) atTop (𝓝 (α/(Real.sqrt (1 - 4*α^2)))) := by
  have ht := t_bounds hα hα'
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one ht.1.le ht.2
  have ha : Tendsto (fun n => t α^((n/2))) atTop (𝓝 0) := hpow.comp aa_tendsto
  have hb : Tendsto (fun n => t α^(((n-1)/2))) atTop (𝓝 0) := hpow.comp bb_tendsto
  have hab : Tendsto (fun n => t α^((n/2)+((n-1)/2))) atTop (𝓝 0) := by
    simpa only [pow_add, mul_zero] using ha.mul hb
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim : Tendsto (fun n => (α/(Real.sqrt (1 - 4*α^2)))*((1-t α^((n/2)))*(1-t α^(((n-1)/2))))/
      (1-t α^((n/2)+((n-1)/2)))) atTop (𝓝 (α/(Real.sqrt (1 - 4*α^2)))) := by
    simpa only [Pi.div_def, sub_zero, mul_one, one_mul, div_one] using! (((h1.sub ha).mul
      (h1.sub hb)).const_mul (α/(Real.sqrt (1 - 4*α^2)))).div
      (h1.sub hab) (by norm_num)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 6] with n hn
  exact (RAB_t hα hα' (by omega) (by omega)).symm

private lemma beta_limit_gt_one {β : ℝ} (hcβ : 1/Real.sqrt 5 < β) (hβ : β < 1/2) :
    1 < β/(Real.sqrt (1 - 4*β^2)) := by
  have hpos : 0 < β := c_bounds.1.trans hcβ
  have hs := s_pos hpos hβ
  have hsq := s_sq hpos hβ
  have hc : (1/Real.sqrt 5 : ℝ)^2=1/5 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  have hbc : (1/Real.sqrt 5 : ℝ)^2 < β^2 := by
    nlinarith [c_bounds.1]
  apply (one_lt_div hs).2
  nlinarith

private lemma R_eventually_gt_one {β : ℝ} (hcβ : 1/Real.sqrt 5 < β) (hβ : β < 1/2) :
    ∀ᶠ n in atTop, 1 < RAB β ((n/2)) (((n-1)/2)) := by
  exact (R_limit (c_bounds.1.trans hcβ) hβ).eventually
    (eventually_gt_nhds (beta_limit_gt_one hcβ hβ))

def claim : Prop :=
  (∀ n, 6 ≤ n → ∃ a, 1 / Real.sqrt 5 < a ∧ a < 1 / 2 ∧ p1 n a = 0) ∧
    ∀ α : ℕ → ℝ, (∀ n, 6 ≤ n → 0 < α n ∧ α n < 1 / 2 ∧ p1 n (α n) = 0) →
      (∀ n, 6 ≤ n → 1 / Real.sqrt 5 < α n) ∧ Tendsto α atTop (𝓝 (1 / Real.sqrt 5))

private lemma root_above_and_tendsto
    (c u : ℝ) (hc : 0 < c) (hcu : c < u)
    (R : ℕ → ℝ → ℝ)
    (hRc : ∀ n, R n c < 1)
    (hstrict : ∀ n, StrictMonoOn (R n) (Set.Ioo 0 u))
    (hbeta : ∀ β : ℝ, c < β → β < u → ∀ᶠ n : ℕ in atTop, 1 < R n β)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < u ∧ R n (α n) = 1) :
    (∀ n, c < α n) ∧ Tendsto α atTop (𝓝 c) := by
  have habove : ∀ n, c < α n := by
    intro n
    by_contra hn
    have hle : α n ≤ c := le_of_not_gt hn
    have hαmem : α n ∈ Set.Ioo 0 u := ⟨(hα n).1, (hα n).2.1⟩
    have hcmem : c ∈ Set.Ioo 0 u := ⟨hc, hcu⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hmono := hstrict n hαmem hcmem hlt
      linarith [hRc n, (hα n).2.2]
    · subst heq
      linarith [hRc n, (hα n).2.2]
  apply And.intro habove
  apply tendsto_order.2
  constructor
  · intro a ha
    have hca : a < c := ha
    filter_upwards [] with n
    exact lt_of_lt_of_le hca (le_of_lt (habove n))
  · intro b hb
    by_cases hbu : u ≤ b
    · filter_upwards [] with n
      exact lt_of_lt_of_le (hα n).2.1 hbu
    · have hbu' : b < u := lt_of_not_ge hbu
      let β : ℝ := (c + b) / 2
      have hcβ : c < β := left_lt_add_div_two.mpr hb
      have hβb : β < b := add_div_two_lt_right.mpr hb
      have hβu : β < u := hβb.trans hbu'
      have hev := hbeta β hcβ hβu
      filter_upwards [hev] with n hn
      have hαβ : α n ≤ β := by
        by_contra hnot
        have hβlt : β < α n := lt_of_not_ge hnot
        have hαmem : α n ∈ Set.Ioo 0 u := ⟨(hα n).1, (hα n).2.1⟩
        have hβmem : β ∈ Set.Ioo 0 u := ⟨by linarith, hβu⟩
        have hmono := hstrict n hβmem hαmem hβlt
        linarith [hmono, (hα n).2.2]
      have : α n < b := lt_of_le_of_lt hαβ hβb
      exact this

private lemma crossing_exists_unique
    (c u : ℝ) (hcu : c < u)
    (R : ℝ → ℝ)
    (hcont : ContinuousOn R (Set.Icc c u))
    (hleft : R c < 1) (hright : 1 < R u)
    (hstrict : StrictMonoOn R (Set.Ioo c u)) :
    ∃! x, x ∈ Set.Ioo c u ∧ R x = 1 := by
  have hmem : (1:ℝ) ∈ Set.Ioo (R c) (R u) := ⟨hleft, hright⟩
  obtain ⟨x, hx, hxeq⟩ := intermediate_value_Ioo hcu.le hcont hmem
  refine ⟨x, ⟨hx, hxeq⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hyI, hyeq⟩
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hxy' | hyx'
  · have hmono := hstrict hyI hx hxy'
    linarith [hmono, hxeq, hyeq]
  · have hmono := hstrict hx hyI hyx'
    linarith [hmono, hxeq, hyeq]

private lemma continuous_d (k : ℕ) : Continuous (fun α : ℝ => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k) := by
  induction k using Nat.twoStepInduction with
  | zero => simpa only [d_zero, d_one, d_step] using (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)))
  | one => simpa only [d_zero, d_one, d_step] using (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)))
  | more k ih0 ih1 =>
    simp only [d_step]
    change Continuous (fun α : ℝ => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (k+1)-α^2*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k)
    exact ih1.sub ((continuous_id.pow 2).mul ih0)

private lemma d_pos_le_half {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1/2) (k : ℕ) : 0 < ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k := by
  rcases lt_or_eq_of_le hα' with hlt | heq
  · exact d_pos hα hlt k
  · rw [heq]; exact d_half_pos k

private lemma R_continuousOn (n : ℕ) :
    ContinuousOn (fun α => RAB α ((n/2)) (((n-1)/2))) (Set.Icc (1/Real.sqrt 5) (1/2)) := by
  unfold RAB
  apply ContinuousOn.div₀
  · exact ((continuous_id.mul (continuous_d _)).mul (continuous_d _)).continuousOn
  · exact (continuous_d _).continuousOn
  · intro α hα
    exact ne_of_gt (d_pos_le_half (c_bounds.1.trans_le hα.1) hα.2 _)

private lemma p1_zero_iff (n : ℕ) (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) :
    p1 n α = 0 ↔ RAB α ((n/2)) (((n-1)/2)) = 1 := by
  rw [p1_reduction n hn hα hα']
  have hf : α*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (n-2)/((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n ≠ 0 :=
    ne_of_gt (div_pos (mul_pos hα (d_pos hα hα' _)) (d_pos hα hα' _))
  rw [mul_eq_zero]
  constructor
  · intro h; rcases h with h | h
    · exact (hf h).elim
    · linarith
  · intro h; right; linarith

private lemma R_crossing (n : ℕ) (hn : 6 ≤ n) (u : ℝ)
    (hu : 1/Real.sqrt 5 < u) (hu' : u ≤ 1/2)
    (hright : 1 < RAB u ((n/2)) (((n-1)/2))) :
    ∃ a, 1/Real.sqrt 5 < a ∧ a < u ∧ RAB a ((n/2)) (((n-1)/2)) = 1 := by
  have ha : 0 < (n/2) := by omega
  have hb : 0 < ((n-1)/2) := by omega
  have hcont : ContinuousOn (fun α => RAB α ((n/2)) (((n-1)/2)))
      (Set.Icc (1/Real.sqrt 5) u) :=
    (R_continuousOn n).mono (by intro x hx; exact ⟨hx.1,hx.2.trans hu'⟩)
  obtain ⟨a,⟨hI,hR⟩,_⟩ := crossing_exists_unique (1/Real.sqrt 5) u hu
    (fun α => RAB α ((n/2)) (((n-1)/2))) hcont (RAB_lt_one_c ha hb) hright
    (by
      intro x hx y hy hxy
      exact RAB_strictMonoOn ha hb ⟨c_bounds.1.trans hx.1,hx.2.trans_le hu'⟩
        ⟨c_bounds.1.trans hy.1,hy.2.trans_le hu'⟩ hxy)
  exact ⟨a,hI.1,hI.2,hR⟩

private lemma R_root_exists (n : ℕ) (hn : 6 ≤ n) :
    ∃ a, 1/Real.sqrt 5 < a ∧ a < 1/2 ∧ RAB a ((n/2)) (((n-1)/2)) = 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact R_crossing 6 (by omega) (1/2) c_bounds.2 le_rfl
      (RAB_half_gt_one_for_indices 6 (by omega))
  | succ n hn ih =>
    obtain ⟨a,hca,ha,hR⟩ := ih
    have hstep := R_strict_succ n hn (c_bounds.1.trans hca) ha
    have hright : 1 < RAB a (((n+1)/2)) ((((n+1)-1)/2)) := lt_of_eq_of_lt hR.symm hstep
    obtain ⟨a',hc',ha',hR'⟩ := R_crossing (n+1) (by omega) a hca ha.le hright
    exact ⟨a',hc',ha'.trans ha,hR'⟩

theorem result : claim := by
  constructor
  · intro n hn
    obtain ⟨a,hca,ha,hR⟩ := R_root_exists n hn
    exact ⟨a,hca,ha,(p1_zero_iff n hn (c_bounds.1.trans hca) ha).2 hR⟩
  · intro α hα
    have hzero (k : ℕ) : 0 < α (k+6) ∧ α (k+6) < 1/2 ∧
        RAB (α (k+6)) (((k+6)/2)) ((((k+6)-1)/2)) = 1 := by
      have hk := hα (k+6) (by omega)
      exact ⟨hk.1,hk.2.1,(p1_zero_iff (k+6) (by omega) hk.1 hk.2.1).1 hk.2.2⟩
    have hres := root_above_and_tendsto (1/Real.sqrt 5) (1/2) c_bounds.1 c_bounds.2
      (fun k x => RAB x (((k+6)/2)) ((((k+6)-1)/2)))
      (by intro k; exact RAB_lt_one_c (by omega) (by omega))
      (by intro k; exact RAB_strictMonoOn (by omega) (by omega))
      (by
        intro β hcβ hβ
        exact (tendsto_add_atTop_nat 6).eventually (R_eventually_gt_one hcβ hβ))
      (fun k => α (k+6)) hzero
    constructor
    · intro n hn
      have hh := hres.1 (n-6)
      simpa only [Nat.sub_add_cancel hn] using hh
    · exact (tendsto_add_atTop_iff_nat 6).1 hres.2

end D5.S1.Recurrence.KatzCutoff.Result
