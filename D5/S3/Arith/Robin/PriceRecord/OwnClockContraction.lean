/- GID: D5/S3/Arith/Robin/PriceRecord/OwnClockContraction
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/OwnClockContraction
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Exact own-clock existence and uniqueness for distinct natural support p>=2, theta>1. -/

/- UNCOMPILED SOURCE CANDIDATE. The definitions logCutoff and responseClock
are the literal cutoff and max response used by the upstream fixed-support
objective. The old theta>=4*card contraction is deliberately removed. The
active coordinates are counted by the integer support itself; the right
derivative is used at a max tie, so no ordinary derivative through a kink is
claimed. -/

import D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.OwnClockContraction

open Real Set Finset
open scoped Topology
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport

/-- The support condition used by this source: only distinct naturals >=2 are
needed. No primality premise occurs anywhere in the clock argument. -/
def naturalSupport (S : Finset ℕ) : Prop := ∀ p ∈ S, 2 ≤ p

/- These are the literal objective-side definitions, not wrappers. -/
def logCutoff (L : ℝ) : ℝ := log (1 + L * log L)

def responseClock (S : Finset ℕ) (L : ℝ) : ℝ :=
  ∑ p ∈ S, max (log (p : ℝ)) (logCutoff L - log (p : ℝ))

private lemma support_nonempty {S : Finset ℕ} (hθ : 1 < theta S) :
    S.Nonempty := by
  by_contra h
  have : S = ∅ := not_nonempty_iff_eq_empty.mp h
  simp [this, theta] at hθ

lemma theta_le_clock_of_naturalSupport {S : Finset ℕ} (hS : naturalSupport S)
    {x : ℕ → ℝ} (hx : admissible S x) : theta S ≤ clock S x := by
  apply sum_le_sum
  intro p hp
  have hpR : (1 : ℝ) < p := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p hp)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hx p hp) (log_pos hpR).le

lemma ray_bounds {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S)
    {L : ℝ} (hL : theta S ≤ L) :
    0 < (S.card : ℝ) ∧ 1 < L ∧ 0 < log L := by
  have hne := support_nonempty hθ
  have hcard : 0 < S.card := hne.card_pos
  have hk : (0 : ℝ) < S.card := by exact_mod_cast hcard
  have h1 : 1 < L := lt_of_lt_of_le hθ hL
  exact ⟨hk, h1, log_pos h1⟩

private lemma cutoff_hasDerivAt {L : ℝ} (hL : 1 < L) :
    HasDerivAt logCutoff ((1 + log L) / (1 + L * log L)) L := by
  have h0 : 0 < L := by linarith
  have hl : 0 < log L := log_pos hL
  have hC : 0 < 1 + L * log L := by positivity
  have hd := ((hasDerivAt_const L (1 : ℝ)).add
    ((hasDerivAt_id L).mul (hasDerivAt_log h0.ne'))).log hC.ne'
  convert hd using 1 <;> dsimp [logCutoff] <;>
    field_simp [h0.ne', hC.ne'] <;> ring

private lemma cutoff_monotoneOn : MonotoneOn logCutoff (Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  have he : exp (-1 : ℝ) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  have hmul : x * log x ≤ y * log y :=
    Real.mul_log_strictMonoOn.monotoneOn (he.trans hx) (he.trans hy) hxy
  change log (1 + x * log x) ≤ log (1 + y * log y)
  have hx0 : 0 < x := by linarith
  have hxlog : 0 ≤ log x := log_nonneg hx
  exact log_le_log (by positivity) (by linarith)

private lemma active_count_le {S : Finset ℕ} (hS : naturalSupport S)
    {r : ℝ} (hr : 1 < r) :
    ((S.filter (fun p => (p : ℝ) ≤ r)).card : ℝ) ≤ r - 1 := by
  classical
  let n : ℕ := ⌊r⌋₊
  by_cases hn : 2 ≤ n
  · have hsub : S.filter (fun p => (p : ℝ) ≤ r) ⊆ Finset.Ico 2 (n + 1) := by
      intro p hp
      have hpS : p ∈ S := (mem_filter.mp hp).1
      have hpr : (p : ℝ) ≤ r := (mem_filter.mp hp).2
      have hp2 : 2 ≤ p := hS p hpS
      have hpn : p ≤ n := Nat.le_floor hpr
      exact mem_Ico.mpr ⟨hp2, Nat.lt_succ_of_le hpn⟩
    have hc := card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hfloor : (n : ℝ) ≤ r := by
      dsimp [n]
      exact Nat.floor_le (by linarith)
    -- Eliminate truncated Nat subtraction before casting the cardinal inequality.
    have hc' : (S.filter (fun p => (p : ℝ) ≤ r)).card + 1 ≤ n := by omega
    have hcR : ((S.filter (fun p => (p : ℝ) ≤ r)).card : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hc'
    linarith
  · have hsub : S.filter (fun p => (p : ℝ) ≤ r) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hpS hpr
      have hp2 : 2 ≤ p := hS p hpS
      have hpn : p ≤ n := Nat.le_floor hpr
      omega
    simpa only [hsub, card_empty, Nat.cast_zero] using (sub_nonneg.mpr hr.le)

private lemma active_count_log_le {S : Finset ℕ} (hS : naturalSupport S)
    {L : ℝ} (hL : 1 < L) :
    ((S.filter (fun p => log (p : ℝ) ≤ logCutoff L - log (p : ℝ))).card : ℝ) ≤
      Real.sqrt (1 + L * log L) - 1 := by
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < log L := log_pos hL
  have harg : 0 < 1 + L * log L := by positivity
  let R : ℝ := Real.sqrt (1 + L * log L)
  have hR : 1 < R := by
    dsimp [R]
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    nlinarith [mul_pos hL0 hlogL]
  have hsub : S.filter (fun p => log (p : ℝ) ≤ logCutoff L - log (p : ℝ)) ⊆
      S.filter (fun p => (p : ℝ) ≤ R) := by
    intro p hp
    have hpS := (mem_filter.mp hp).1
    have hp0 : 0 < (p : ℝ) := by
      exact_mod_cast (by linarith [hS p hpS] : 0 < p)
    have hpineq := (mem_filter.mp hp).2
    have hpow : (p : ℝ) ^ (2 : ℕ) ≤ 1 + L * log L := by
      have h2 : log ((p : ℝ) ^ (2 : ℕ)) ≤ logCutoff L := by
        rw [log_pow]
        linarith
      have hlog := (log_le_iff_le_exp (show 0 < (p : ℝ) ^ 2 by positivity)).mp h2
      simpa [logCutoff, Real.exp_log harg] using hlog
    have hpR : (p : ℝ) ≤ R := by
      dsimp [R]
      exact (Real.le_sqrt hp0.le harg.le).mpr hpow
    exact mem_filter.mpr ⟨hpS, hpR⟩
  have hc : ((S.filter (fun p => log (p : ℝ) ≤ logCutoff L - log (p : ℝ))).card : ℝ) ≤
      ((S.filter (fun p => (p : ℝ) ≤ R)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hc.trans (active_count_le hS hR)

private def responseEnvelope (L : ℝ) : ℝ :=
  let R := Real.sqrt (1 + L * log L)
  (R - 1) * (1 + log L) / (1 + L * log L)

private lemma log_lt_response_radius {L : ℝ} (hL : 1 < L) :
    log L < Real.sqrt (1 + L * log L) := by
  have hu : 0 < log L := log_pos hL
  have hlt : log L < L := by
    have := Real.log_lt_sub_one_of_pos (show 0 < L by linarith) (ne_of_gt hL)
    linarith
  have hmul := mul_lt_mul_of_pos_right hlt hu
  have hsq : (log L) ^ 2 < 1 + L * log L := by nlinarith
  exact Real.lt_sqrt_of_sq_lt hsq

private lemma response_envelope_lt_one {L : ℝ} (hL : 1 < L) :
    responseEnvelope L < 1 := by
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < log L := log_pos hL
  have hR : 1 < Real.sqrt (1 + L * log L) := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    nlinarith [mul_pos hL0 hlogL]
  have hlog := log_lt_response_radius hL
  dsimp [responseEnvelope]
  have hden : 0 < 1 + L * log L := by positivity
  apply (div_lt_iff₀ hden).mpr
  have hmul := mul_lt_mul_of_pos_left
    (show 1 + log L < 1 + Real.sqrt (1 + L * log L) by linarith)
    (show 0 < Real.sqrt (1 + L * log L) - 1 by linarith)
  nlinarith [Real.sq_sqrt hden.le]

private lemma response_continuousOn {S : Finset ℕ} {u v : ℝ} (hu : 1 < u)
    (huv : u ≤ v) : ContinuousOn (responseClock S) (Icc u v) := by
  have hcut : ContinuousOn logCutoff (Icc u v) := by
    intro L hL
    exact (cutoff_hasDerivAt (lt_of_lt_of_le hu hL.1)).continuousAt.continuousWithinAt
  apply continuousOn_finsetSum
  intro p hp L hL
  exact (continuousOn_const.max (hcut.sub continuousOn_const)) hL

/- At a tie, logCutoff is increasing on the right ray, so the right derivative
is the active branch. This is the only derivative statement about max used by
the scalar argument. -/
private lemma response_hasDerivWithinAt_right {S : Finset ℕ} {u v L : ℝ}
    (hS : naturalSupport S) (hu : 1 < u) (hL : L ∈ Ico u v) :
    HasDerivWithinAt (responseClock S)
      (∑ p ∈ S, if log (p : ℝ) ≤ logCutoff L - log (p : ℝ)
        then (1 + log L) / (1 + L * log L) else 0) (Ici L) L := by
  classical
  have hcut := cutoff_hasDerivAt (lt_of_lt_of_le hu hL.1)
  have hmono : MonotoneOn logCutoff (Ici L) :=
    cutoff_monotoneOn.mono (Ici_subset_Ici.mpr (le_trans (le_of_lt hu) hL.1))
  have hterm (p : ℕ) :
      HasDerivWithinAt (fun t : ℝ => max (log (p : ℝ))
        (logCutoff t - log (p : ℝ)))
        (if log (p : ℝ) ≤ logCutoff L - log (p : ℝ)
          then (1 + log L) / (1 + L * log L) else 0) (Ici L) L := by
    by_cases hp : log (p : ℝ) ≤ logCutoff L - log (p : ℝ)
    · have heq : ∀ t ∈ Ici L,
          max (log (p : ℝ)) (logCutoff t - log (p : ℝ)) =
            logCutoff t - log (p : ℝ) := by
        intro t ht
        exact max_eq_right (hp.trans
          (sub_le_sub_right (hmono (show L ∈ Ici L from le_rfl) ht ht) _))
      rw [if_pos hp]
      exact (hcut.sub_const (log (p : ℝ))).hasDerivWithinAt.congr_of_mem heq le_rfl
    · have hp' : logCutoff L - log (p : ℝ) < log (p : ℝ) := lt_of_not_ge hp
      have hlt : ∀ᶠ t in 𝓝[Ici L] L,
          logCutoff t - log (p : ℝ) < log (p : ℝ) :=
        (hcut.continuousAt.sub continuousAt_const).continuousWithinAt.eventually
          (eventually_lt_nhds hp')
      have heq : ∀ᶠ t in 𝓝[Ici L] L,
          max (log (p : ℝ)) (logCutoff t - log (p : ℝ)) = log (p : ℝ) := by
        filter_upwards [hlt] with t ht
        exact max_eq_left ht.le
      rw [if_neg hp]
      exact (hasDerivAt_const L (log (p : ℝ))).hasDerivWithinAt.congr_of_eventuallyEq
        heq (max_eq_left hp'.le)
  simpa only [responseClock] using
    (HasDerivWithinAt.fun_sum (u := S) (fun p _ => hterm p))

private lemma response_derivative_le_envelope {S : Finset ℕ} (hS : naturalSupport S)
    {u v L : ℝ} (hu : 1 < u) (hL : L ∈ Ico u v) :
    (∑ p ∈ S, if log (p : ℝ) ≤ logCutoff L - log (p : ℝ)
      then (1 + log L) / (1 + L * log L) else 0) ≤ responseEnvelope L := by
  have hL1 : 1 < L := lt_of_lt_of_le hu hL.1
  have hlogL : 0 < log L := log_pos hL1
  have hL0 : 0 < L := by linarith
  have hd : 0 ≤ (1 + log L) / (1 + L * log L) := by positivity
  have hcount := active_count_log_le hS hL1
  have hsum : (∑ p ∈ S, if log (p : ℝ) ≤ logCutoff L - log (p : ℝ)
      then (1 + log L) / (1 + L * log L) else 0) =
      (S.filter (fun p => log (p : ℝ) ≤ logCutoff L - log (p : ℝ))).card *
        ((1 + log L) / (1 + L * log L)) := by
    rw [← Finset.sum_filter]
    simp only [sum_const, nsmul_eq_mul]
  rw [hsum]
  dsimp [responseEnvelope]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hcount hd

private lemma log_le_two_thirds_radius {L : ℝ} (hL : 1 < L) :
    log L < (2 / 3 : ℝ) * Real.sqrt (1 + L * log L) := by
  have hL0 : 0 < L := by linarith
  have hlog : 0 < log L := log_pos hL
  have hratio : 0 < L / Real.exp 1 := by positivity
  have hlogratio := Real.log_le_sub_one_of_pos hratio
  have hlogexp : Real.log (L / Real.exp 1) = log L - 1 := by
    rw [Real.log_div (ne_of_gt hL0) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  have hehalf : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    simpa using (add_one_le_exp (1 / 2 : ℝ))
  have heone : (9 / 4 : ℝ) ≤ Real.exp 1 := by
    rw [show (1 : ℝ) = (1 / 2 : ℝ) + 1 / 2 by norm_num, Real.exp_add]
    have hmul := mul_le_mul hehalf hehalf (by norm_num : (0 : ℝ) ≤ 3 / 2)
      (by positivity : (0 : ℝ) ≤ Real.exp (1 / 2 : ℝ))
    nlinarith
  have hlog_le : log L ≤ (4 / 9 : ℝ) * L := by
    rw [hlogexp] at hlogratio
    have hdiv : L / Real.exp 1 ≤ (4 / 9 : ℝ) * L := by
      apply (div_le_iff₀ (Real.exp_pos 1)).mpr
      nlinarith [heone]
    linarith
  have hsq : (log L) ^ 2 < (4 / 9 : ℝ) * (1 + L * log L) := by
    have hlt : log L < L := by
      have hh := Real.log_lt_sub_one_of_pos hL0 (ne_of_gt hL)
      linarith
    have hmul := mul_lt_mul_of_pos_right hlt hlog
    nlinarith [hlog_le]
  have hR0 : 0 ≤ Real.sqrt (1 + L * log L) := Real.sqrt_nonneg _
  have hR : 0 < Real.sqrt (1 + L * log L) := by
    positivity
  have hsqrt := Real.lt_sqrt_of_sq_lt hsq
  have hsq' : (3 * log L) ^ 2 < (2 * Real.sqrt (1 + L * log L)) ^ 2 := by
    nlinarith [hsq]
  nlinarith [hsq']

private lemma response_envelope_global {L : ℝ} (hL : 1 < L) :
    responseEnvelope L ≤ (25 / 36 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hlog : 0 < log L := log_pos hL
  let R : ℝ := Real.sqrt (1 + L * log L)
  have hR : 1 < R := by
    dsimp [R]
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    nlinarith [mul_pos hL0 hlog]
  have hlogR := log_le_two_thirds_radius hL
  have hquad : 36 * (R - 1) * (1 + log L) ≤ 25 * R ^ 2 := by
    have hfirst : 36 * (R - 1) * (1 + log L) ≤
        24 * R ^ 2 + 12 * R - 36 := by
      have hnon : 0 ≤ R - 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hlogR.le (by nlinarith : 0 ≤ 36 * (R - 1))]
    have hsquare : 0 ≤ (R - 6) ^ 2 := sq_nonneg (R - 6)
    nlinarith [hfirst, hsquare]
  dsimp [responseEnvelope, R]
  have hden : 0 < 1 + L * log L := by positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith [hquad]

private lemma response_derivative_le_global {S : Finset ℕ} (hS : naturalSupport S)
    {u v L : ℝ} (hu : 1 < u) (hL : L ∈ Ico u v) :
    (∑ p ∈ S, if log (p : ℝ) ≤ logCutoff L - log (p : ℝ)
      then (1 + log L) / (1 + L * log L) else 0) ≤ (25 / 36 : ℝ) := by
  exact (response_derivative_le_envelope hS hu hL).trans
    (response_envelope_global (lt_of_lt_of_le hu hL.1))

private lemma response_increment_le_global {S : Finset ℕ} (hS : naturalSupport S)
    {u v : ℝ} (hu : 1 < u) (huv : u < v) :
    responseClock S v - responseClock S u ≤ (25 / 36 : ℝ) * (v - u) := by
  have hcont : ContinuousOn (responseClock S) (Icc u v) :=
    response_continuousOn hu huv.le
  have hderiv := fun L (hL : L ∈ Ico u v) =>
    response_hasDerivWithinAt_right hS hu hL
  have hbound : ∀ L ∈ Ico u v, (∑ p ∈ S, if log (p : ℝ) ≤ logCutoff L - log (p : ℝ)
      then (1 + log L) / (1 + L * log L) else 0) ≤ (25 / 36 : ℝ) := by
    intro L hL
    exact response_derivative_le_global hS hu hL
  let E : ℝ → ℝ := fun t => responseClock S u + (25 / 36 : ℝ) * (t - u)
  have hEderiv : ∀ L ∈ Ico u v, HasDerivWithinAt E (25 / 36 : ℝ) (Ici L) L := by
    intro L hL
    simpa only [E, id_eq, mul_one] using
      ((((hasDerivAt_id L).sub_const u).const_mul (25 / 36 : ℝ)).const_add
        (responseClock S u)).hasDerivWithinAt
  have hEcont : ContinuousOn E (Icc u v) :=
    continuousOn_const.add
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hle := image_le_of_deriv_right_le_deriv_boundary hcont hderiv
    (show responseClock S u ≤ E u by simp [E]) hEcont hEderiv hbound
  have hq := hle (right_mem_Icc.2 huv.le)
  dsimp [E] at hq
  linarith

theorem response_global_lipschitz {S : Finset ℕ} (hS : naturalSupport S)
    {H s t : ℝ} (hH : 1 < H) (hs : H ≤ s) (ht : H ≤ t) :
    |responseClock S t - responseClock S s| ≤ (25 / 36 : ℝ) * |t - s| := by
  rcases le_total s t with hst | hts
  · by_cases heq : s = t
    · subst t
      simp
    · have hinc := response_increment_le_global hS (lt_of_lt_of_le hH hs) (lt_of_le_of_ne hst heq)
      rw [abs_of_nonneg (sub_nonneg.mpr hst), abs_of_nonneg (sub_nonneg.mpr hst)]
      exact hinc
  · by_cases heq : t = s
    · subst s
      simp
    · have hinc := response_increment_le_global hS (lt_of_lt_of_le hH ht) (lt_of_le_of_ne hts heq)
      rw [abs_of_nonpos (sub_nonpos.mpr hts), abs_of_nonpos (sub_nonpos.mpr hts)]
      nlinarith

private lemma response_interval_contracts {S : Finset ℕ} (hS : naturalSupport S)
    {u v : ℝ} (hu : 1 < u) (huv : u < v) :
    responseClock S v - v < responseClock S u - u := by
  have hinc := response_increment_le_global hS hu huv
  have hstep : (25 / 36 : ℝ) * (v - u) < v - u := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right (by norm_num : (25 / 36 : ℝ) < 1)
      (sub_pos.mpr huv)
  linarith

lemma response_selfmap (S : Finset ℕ) (L : ℝ) : theta S ≤ responseClock S L := by
  exact sum_le_sum (fun p _ => le_max_left (log (p : ℝ)) _)

theorem response_strictAntiOn {S : Finset ℕ} (hS : naturalSupport S)
    {u v : ℝ} (hu : 1 < u) (huv : u < v) :
    responseClock S v - v < responseClock S u - u :=
  response_interval_contracts hS hu huv

private lemma upper_clock_bound {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) :
    responseClock S ((theta S + 4 * (S.card : ℝ)) ^ 2) <
      (theta S + 4 * (S.card : ℝ)) ^ 2 := by
  let H := theta S
  let r := H + 4 * (S.card : ℝ)
  have hH : 1 < H := hθ
  have hH0 : 0 < H := by linarith
  have hr : 1 < r := by
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast (support_nonempty hθ).card_pos
    dsimp only [r]
    linarith
  have hr0 : 0 < r := by linarith
  have hlog : log r ≤ r - 1 := by
    exact le_of_lt (Real.log_lt_sub_one_of_pos (by linarith) (by linarith))
  have hA : logCutoff (r ^ 2) ≤ 4 * log r := by
    have hr2 : 1 < r ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left
      (log_le_sub_one_of_pos (by positivity : 0 < r ^ 2)) (sq_nonneg r)
    have hsq : 1 + r ^ 2 * log (r ^ 2) ≤ r ^ 4 := by nlinarith
    dsimp [logCutoff]
    have hlogr2 : 0 < log (r ^ 2) := log_pos hr2
    have := log_le_log (show 0 < 1 + r ^ 2 * log (r ^ 2) by positivity) hsq
    simpa only [log_pow, Nat.cast_ofNat] using this
  have hterm (p : ℕ) (hp : p ∈ S) :
      max (log (p : ℝ)) (logCutoff (r ^ 2) - log (p : ℝ)) ≤
        log (p : ℝ) + 4 * log r := by
    have hlogr : 0 ≤ log r := log_nonneg (le_of_lt hr)
    have hlogp : 0 ≤ log (p : ℝ) := log_nonneg (by
      exact_mod_cast (show 1 ≤ p from le_trans (by norm_num) (hS p hp)))
    exact max_le (by linarith) (by linarith [hA])
  have hsum : responseClock S (r ^ 2) ≤
      ∑ p ∈ S, (log (p : ℝ) + 4 * log r) := by
    rw [responseClock]
    exact sum_le_sum (fun p hp => hterm p hp)
  have hsum' : (∑ p ∈ S, (log (p : ℝ) + 4 * log r)) =
      H + 4 * (S.card : ℝ) * log r := by
    rw [sum_add_distrib]
    simp only [sum_const, nsmul_eq_mul]
    rw [show (∑ p ∈ S, log (p : ℝ)) = H by rfl]
    ring
  have hcard : (0 : ℝ) ≤ S.card := by positivity
  rw [hsum'] at hsum
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 4 * (S.card : ℝ) by positivity)
  have hid : r ^ 2 - (H + 4 * (S.card : ℝ) * (r - 1)) =
      H * (r - 1) + 4 * (S.card : ℝ) := by dsimp [r]; ring
  have hpos : 0 < H * (r - 1) + 4 * (S.card : ℝ) :=
    add_pos_of_pos_of_nonneg (mul_pos hH0 (sub_pos.mpr hr)) (by positivity)
  have hfinal : H + 4 * (S.card : ℝ) * log r < r ^ 2 := by linarith
  exact hsum.trans_lt hfinal

/-- The scalar clock exists by IVT on the actual max response. Its uniqueness
uses the strict decrease of responseClock-id, including all tie points. -/
theorem exists_unique_clock {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) :
    ∃! L : ℝ, theta S ≤ L ∧ responseClock S L = L := by
  let H := theta S
  let U := (H + 4 * (S.card : ℝ)) ^ 2
  have hHU : H ≤ U := by
    have hc : 0 < (S.card : ℝ) := by
      exact_mod_cast (support_nonempty hθ).card_pos
    have hbase : H ≤ H + 4 * (S.card : ℝ) := by linarith
    have hbase1 : 1 < H + 4 * (S.card : ℝ) := by
      have : 1 < H := hθ
      linarith
    have hsq : H + 4 * (S.card : ℝ) ≤ (H + 4 * (S.card : ℝ)) ^ 2 := by
      simpa only [one_mul, pow_two] using
        mul_le_mul_of_nonneg_right hbase1.le
          (show 0 ≤ H + 4 * (S.card : ℝ) by linarith)
    exact hbase.trans hsq
  have hH1 : 1 < H := hθ
  have hcont : ContinuousOn (fun t : ℝ => responseClock S t - t) (Icc H U) := by
    exact (response_continuousOn hH1 hHU).sub continuousOn_id
  have hleft : 0 ≤ responseClock S H - H := by
    linarith [response_selfmap S H]
  have hright : responseClock S U - U < 0 := by
    dsimp [U, H]
    have h := upper_clock_bound hS hθ
    linarith
  obtain ⟨L, hL, hroot⟩ := intermediate_value_Icc' hHU hcont
    ⟨le_of_lt hright, hleft⟩
  refine ⟨L, ⟨hL.1, by linarith [hroot]⟩, ?_⟩
  intro M hM
  rcases lt_trichotomy M L with hlt | heq | hgt
  · have hdec := response_strictAntiOn hS (lt_of_lt_of_le hH1 hM.1) hlt
    linarith [hM.2, hroot]
  · exact heq
  · have hdec := response_strictAntiOn hS (lt_of_lt_of_le hH1 hL.1) hgt
    linarith [hM.2, hroot]

end D5.S3.Arith.Robin.PriceRecord.OwnClockContraction
