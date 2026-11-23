/- GID: D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumPhaseCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A logarithmic retained-mass floor and finite frequency gaps give uniform window recurrence. -/

import D5.S3.Analytic.Oscillation.OrdinateCounting
import D5.S3.Fourier.WeightedPhaseRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative recurrence for a weighted sine polynomial on growing finite spectral cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff

open D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open D5.S3.Fourier.WeightedPhaseRecurrence (phaseLoss weighted_phase_recurrence)

variable (S : Spectrum) (w : S.index → ℝ)

/-- Total weight through the inclusive spectral cutoff. -/
def mass (T : ℝ) : ℝ :=
  ∑ j ∈ S.cut T, w j

/-- Sine polynomial with the same spectral weights and cutoff. -/
def sine (T v : ℝ) : ℝ :=
  ∑ j ∈ S.cut T, w j * Real.sin (S.gamma j * v)

theorem mem_cut {S : Spectrum} {X : ℝ} {j : S.index} :
    j ∈ S.cut X ↔ S.gamma j ≤ X :=
  (S.finite_le X).mem_toFinset

/-- Each fixed coefficient box admits an eventual exponential separation estimate. -/
def HasBoxGap : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, ∀ᶠ X : ℝ in atTop,
    ∀ k : S.cut X → ℤ, (∃ j, k j ≠ 0) → (∀ j, |k j| ≤ (M : ℤ)) →
      C * Real.exp (-(X ^ (1 + η))) ≤ |∑ j, (k j : ℝ) * S.gamma j.val|

/-- The recurrence budget eventually holds at the power cutoff. -/
private theorem eventual_time_budget {B : ℝ} (hB : 0 < B)
    (hd : ∀ᶠ X : ℝ in atTop, ((S.cut X).card : ℝ) ≤ B * (X * Real.log X))
    {C r α β η ε₀ : ℝ} {N : ℕ}
    (hC : 0 < C) (hr : 0 < r) (hα : 0 < α) (hη : 0 < η)
    (hpower : α * (1 + η) < β) (hN : 0 < N) (hε : 1 / (N : ℝ) < ε₀) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (T ^ β) * (C * Real.exp (-((T ^ α) ^ (1 + η))) / r) *
          (ε₀ - 1 / (N : ℝ)) >
        2 * (ε₀ * (N : ℝ) ^ (S.cut (T ^ α)).card -
          (ε₀ - 1 / (N : ℝ))) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hgap : 0 < ε₀ - 1 / (N : ℝ) := sub_pos.mpr hε
  have hεpos : 0 < ε₀ := (by positivity : 0 < 1 / (N : ℝ)).trans hε
  let K : ℝ := 2 * ε₀ * r / (C * (ε₀ - 1 / (N : ℝ)))
  have hK : 0 < K := by dsimp [K]; positivity
  have hX : Tendsto (fun T : ℝ => T ^ α) atTop atTop := tendsto_rpow_atTop hα
  have hlog : ∀ᶠ X : ℝ in atTop, Real.log X ≤ X ^ η := by
    filter_upwards [(isLittleO_log_rpow_atTop hη).bound (show (0 : ℝ) < 1 by norm_num),
      eventually_ge_atTop (1 : ℝ)] with X hbound hX1
    change ‖Real.log X‖ ≤ 1 * ‖X ^ η‖ at hbound
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hX1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _), one_mul] using hbound
  let κ := α * (1 + η)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hgrow := (tendsto_rpow_atTop (sub_pos.mpr hpower)).eventually_gt_atTop
    (1 + B * Real.log (N : ℝ) + |Real.log K|)
  filter_upwards [hX.eventually hd, hX.eventually hlog, hgrow,
    eventually_ge_atTop (1 : ℝ)] with T hdT hlogT hgrowT hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hXpos : 0 < T ^ α := Real.rpow_pos_of_pos hTpos _
  have hpow : (T ^ α) ^ (1 + η) = T ^ κ := (Real.rpow_mul hTpos.le _ _).symm
  have hpowge : 1 ≤ T ^ κ := Real.one_le_rpow hT hκ.le
  have hdim : ((S.cut (T ^ α)).card : ℝ) * Real.log (N : ℝ) ≤
      (B * Real.log (N : ℝ)) * T ^ κ := by
    calc
      _ ≤ (B * (T ^ α * Real.log (T ^ α))) * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_right hdT hlogN
      _ = (B * Real.log (N : ℝ)) * (T ^ α * Real.log (T ^ α)) := by ring
      _ ≤ (B * Real.log (N : ℝ)) * (T ^ α * (T ^ α) ^ η) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogT hXpos.le)
          (mul_nonneg hB.le hlogN)
      _ = _ := by rw [← hpow, Real.rpow_add hXpos, Real.rpow_one]
  have hmain : (1 + B * Real.log (N : ℝ) + |Real.log K|) * T ^ κ < T ^ β := by
    calc
      _ < T ^ (β - κ) * T ^ κ := mul_lt_mul_of_pos_right hgrowT
        (Real.rpow_pos_of_pos hTpos _)
      _ = _ := by rw [← Real.rpow_add hTpos]; congr 1; ring
  have hconst : Real.log K ≤ |Real.log K| * T ^ κ :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hpowge)
  have hlt :
      Real.log K + ((S.cut (T ^ α)).card : ℝ) * Real.log (N : ℝ) <
        T ^ β - (T ^ α) ^ (1 + η) := by
    rw [hpow]
    linarith
  have hexp := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_add, Real.exp_log hK, Real.exp_nat_mul,
    Real.exp_log (zero_lt_one.trans_le hNreal), Real.exp_sub] at hexp
  have hscaled := mul_lt_mul_of_pos_left hexp (show 0 < C * (ε₀ - 1 / (N : ℝ)) / r
    from div_pos (mul_pos hC hgap) hr)
  have heq : (C * (ε₀ - 1 / (N : ℝ)) / r) * (K * (N : ℝ) ^ (S.cut (T ^ α)).card) =
      2 * (ε₀ * (N : ℝ) ^ (S.cut (T ^ α)).card) := by
    change (C * (ε₀ - 1 / (N : ℝ)) / r) *
      (2 * ε₀ * r / (C * (ε₀ - 1 / (N : ℝ))) * (N : ℝ) ^ (S.cut (T ^ α)).card) = _
    have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
    have hnumer : ε₀ * (N : ℝ) - 1 ≠ 0 :=
      (sub_pos.mpr ((div_lt_iff₀ hNpos).mp hε)).ne'
    field_simp [ne_of_gt hC, ne_of_gt hr, hNpos.ne', hnumer]
  rw [heq, div_eq_mul_inv (Real.exp (T ^ β)), ← Real.exp_neg] at hscaled
  linarith only [show
    (C * (ε₀ - 1 / (N : ℝ)) / r) *
          (Real.exp (T ^ β) * Real.exp (-((T ^ α) ^ (1 + η)))) =
        Real.exp (T ^ β) * (C * Real.exp (-((T ^ α) ^ (1 + η))) / r) *
          (ε₀ - 1 / (N : ℝ)) by ring, hscaled, hgap]

private theorem tail_loss_bound (hw : ∀ j, 0 ≤ w j) {X T : ℝ} (hXT : X ≤ T)
    (hWX : 0 < mass S w X) (hWT : 0 < mass S w T) {v ε₀ : ℝ}
    (hsmall : 1 - sine S w X v / mass S w X < ε₀) :
    1 - sine S w T v / mass S w T <
      2 * (1 - mass S w X / mass S w T) +
        (mass S w X / mass S w T) * ε₀ := by
  classical
  let f (j : S.index) : ℝ := w j * Real.sin (S.gamma j * v)
  have hsub : S.cut X ⊆ S.cut T :=
    fun _ hj => mem_cut.mpr ((mem_cut.mp hj).trans hXT)
  have hW := Finset.sum_sdiff (f := w) hsub
  have hF := Finset.sum_sdiff (f := f) hsub
  change (∑ j ∈ S.cut T \ S.cut X, w j) +
    mass S w X = mass S w T at hW
  change (∑ j ∈ S.cut T \ S.cut X, f j) +
    sine S w X v = sine S w T v at hF
  have hn : -(∑ j ∈ S.cut T \ S.cut X, w j) ≤
      ∑ j ∈ S.cut T \ S.cut X, f j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    simpa only [f, mul_neg, mul_one] using
      mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (S.gamma j * v))
        (hw j)
  have hsmall' := (div_lt_iff₀ hWX).mp (show
      (mass S w X - sine S w X v) / mass S w X < ε₀ by
    rwa [sub_div, div_self hWX.ne'])
  have hfull : mass S w T - sine S w T v <
      2 * (mass S w T - mass S w X) + mass S w X * ε₀ := by
    linarith only [hW, hF, hn, hsmall']
  have hdiv := div_lt_div_of_pos_right hfull hWT
  rw [sub_div, div_self hWT.ne'] at hdiv
  convert hdiv using 1
  field_simp [hWT.ne']

private theorem choose_cutoff_parameters {β ε : ℝ} (hβ : 0 < β)
    (hε : 2 * (1 - (min β 1)^2) < ε) :
    ∃ α η ε₀ : ℝ, 0 < α ∧ α < min β 1 ∧ 0 < η ∧ α * (1 + η) < β ∧
      0 < ε₀ ∧ ε₀ ≤ 1 ∧ 2 * (1 - α^2) + α^2 * ε₀ < ε := by
  let m := min β 1
  have hm : 0 < m := lt_min hβ zero_lt_one
  have hcont : Continuous (fun x : ℝ => 2 * (1 - x^2)) := by fun_prop
  have hev := hcont.continuousAt (x := m) (gt_mem_nhds hε)
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let h := min (d / 2) (m / 2)
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have hhd : h < d := (min_le_left _ _).trans_lt (by linarith)
  have hhm : h < m := (min_le_right _ _).trans_lt (by linarith)
  let α := m - h
  have hα : 0 < α := sub_pos.mpr hhm
  have hαm : α < m := sub_lt_self m hh
  have hnear : dist α m < d := by
    rw [Real.dist_eq, show α - m = -h by dsimp [α]; ring, abs_neg, abs_of_pos hh]
    exact hhd
  have hslack : 2 * (1 - α^2) < ε := hball hnear
  have hαβ : α < β := hαm.trans_le (min_le_left _ _)
  have hαone : α < 1 := hαm.trans_le (min_le_right _ _)
  have h1 : 1 < β / α := (lt_div_iff₀ hα).mpr (by simpa using hαβ)
  obtain ⟨z, hz₁, hz₂⟩ := exists_between h1
  refine ⟨α, z - 1, min 1 ((ε - 2 * (1 - α^2)) / 2), hα, hαm, sub_pos.mpr hz₁, ?_, ?_, min_le_left _ _, ?_⟩
  · have hz := (lt_div_iff₀ hα).mp hz₂
    linarith only [hz, show α * (1 + (z - 1)) = z * α by ring]
  · exact lt_min zero_lt_one (by positivity)
  · have hαsq : α^2 ≤ 1 := by nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hαone.le)]
    have hm := mul_le_mul_of_nonneg_right hαsq
      (show 0 ≤ (ε - 2 * (1 - α^2)) / 2 by positivity)
    have hmin := mul_le_mul_of_nonneg_left
      (min_le_right (1 : ℝ) ((ε - 2 * (1 - α^2)) / 2)) (sq_nonneg α)
    linarith

private theorem cutoff_recurrence (hw : ∀ j, 0 ≤ w j)
    {η C r X ε₀ R : ℝ} {N : ℕ} (hC : 0 < C) (hr : 0 < r)
    (hcoeff : ∀ k : S.cut X → ℤ, (∃ j, k j ≠ 0) → (∀ j, |k j| ≤ (N : ℤ)) →
      C * Real.exp (-(X ^ (1 + η))) ≤ |∑ j, (k j : ℝ) * S.gamma j.val|)
    (hN : 0 < N)
    (hε : 1 / (N : ℝ) < ε₀) (hW : 0 < mass S w X)
    (hR : R * (C * Real.exp (-(X ^ (1 + η))) / r) * (ε₀ - 1 / (N : ℝ)) >
      2 * (ε₀ * (N : ℝ) ^ (S.cut X).card - (ε₀ - 1 / (N : ℝ)))) :
    ∀ a : ℝ, ∃ u ∈ Icc a (a + R),
      1 - sine S w X (u / r) / mass S w X < ε₀ := by
  classical
  let K := S.cut X
  let p : K → ℝ := fun j => w j.val / mass S w X
  let g : K → ℝ := fun j => S.gamma j.val / r
  let θ : K → ℝ := fun _ => Real.pi / 2
  let δ := C * Real.exp (-(X ^ (1 + η))) / r
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hp (j : K) : 0 ≤ p j := div_nonneg (hw j.val) hW.le
  have hp1 : ∑ j : K, p j = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div, Finset.sum_coe_sort, ← show mass S w X =
      ∑ j ∈ K, w j from rfl, div_self hW.ne']
  have hmodes (k : K → ℤ) (hk : ∀ j, |k j| ≤ (N : ℤ)) (hnz : ∃ j, k j ≠ 0) :
      δ ≤ |∑ j, (k j : ℝ) * g j| := by
    have hbound := hcoeff k hnz hk
    refine (div_le_iff₀ hr).mpr ?_
    rw [← abs_of_pos hr, ← abs_mul, Finset.sum_mul]
    convert hbound using 2
    apply Finset.sum_congr rfl
    intro j _
    change (k j : ℝ) * (S.gamma j.val / r) * r = (k j : ℝ) * S.gamma j.val
    field_simp
  have hres (k : K → ℤ) (hk : ∀ j, |k j| ≤ (N : ℤ))
      (hz : (∑ j, (k j : ℝ) * g j) = 0) : Real.cos (∑ j, (k j : ℝ) * θ j) = 1 := by
    have hz' : ∀ j, k j = 0 := by
      intro j
      by_contra h
      have hbound := hmodes k hk ⟨j, h⟩
      rw [hz, abs_zero] at hbound
      exact (not_le_of_gt hδ) hbound
    simp [hz']
  have hnonres (k : K → ℤ) (hk : ∀ j, |k j| ≤ (N : ℤ))
      (hnz : (∑ j, (k j : ℝ) * g j) ≠ 0) : δ ≤ |∑ j, (k j : ℝ) * g j| := by
    apply hmodes k hk
    by_contra! h
    exact hnz (by simp [h])
  have hbudget : R * δ * (ε₀ - 1 / (N : ℝ)) >
      2 * (ε₀ * (N : ℝ) ^ Fintype.card K - (ε₀ - 1 / (N : ℝ))) := by
    rw [Fintype.card_coe]
    exact hR
  intro a
  obtain ⟨u, hu, hloss⟩ :=
    weighted_phase_recurrence g θ p N ε₀ δ a R hN hp hp1 hε hδ hres hnonres hbudget
  have hscore : (∑ j : K, p j * Real.cos (g j * u - θ j)) =
      sine S w X (u / r) / mass S w X := by
    calc
      _ = ∑ j : K,
          (w j.val * Real.sin (S.gamma j.val * (u / r))) / mass S w X := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show θ j = Real.pi / 2 from rfl, Real.cos_sub_pi_div_two,
          show g j * u = S.gamma j.val * (u / r) by dsimp only [g]; ring]
        dsimp only [p]
        ring
      _ = _ := by
        rw [← Finset.sum_div,
          Finset.sum_coe_sort K (fun j => w j * Real.sin (S.gamma j * (u / r)))]
        rfl
  simp only [phaseLoss, mul_sub, mul_one, Finset.sum_sub_distrib, hp1, hscore] at hloss
  exact ⟨u, hu, hloss⟩

/-- A lower asymptotic retained-mass fraction and fixed-box frequency separation give
recurrence in every translated window of the stated length. -/
theorem eventual_sine_cutoff_tradeoff
    (hw : ∀ j, 0 ≤ w j) (hpos : ∀ᶠ T : ℝ in atTop, 0 < mass S w T)
    (hd : ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ((S.cut X).card : ℝ) ≤ B * (X * Real.log X))
    (hgap : HasBoxGap S)
    (hratio : ∀ α : ℝ, 0 < α → α < 1 → ∃ q : ℝ, α^2 ≤ q ∧
      Tendsto (fun T : ℝ => mass S w (T ^ α) / mass S w T) atTop (nhds q))
    {r β ε : ℝ} (hr : 0 < r) (hβ : 0 < β) (hε : 2 * (1 - (min β 1)^2) < ε) :
    ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ a : ℝ, ∃ u ∈ Icc a (a + Real.exp (T ^ β)),
        1 - sine S w T (u / r) / mass S w T < ε := by
  obtain ⟨α, η, ε₀, hα, hαmin, hη, hpower, hε₀, hε₀le, hlose⟩ :=
    choose_cutoff_parameters hβ hε
  obtain ⟨N, hNbig⟩ := exists_nat_gt (1 / ε₀)
  have hNreal : (0 : ℝ) < N := (by positivity : 0 < 1 / ε₀).trans hNbig
  have hN : 0 < N := by exact_mod_cast hNreal
  have hNε : 1 / (N : ℝ) < ε₀ := by
    apply (div_lt_iff₀ hNreal).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε₀).mp hNbig
  obtain ⟨B, hB, hdimension⟩ := hd
  obtain ⟨C, hC, hcoeff⟩ := hgap η hη
  obtain ⟨q, hq, hqLimit⟩ := hratio α hα (hαmin.trans_le (min_le_right _ _))
  have hX := tendsto_rpow_atTop hα
  have hcont : Continuous (fun z : ℝ => 2 * (1 - z) + z * ε₀) := by fun_prop
  have hqsmall : 2 * (1 - q) + q * ε₀ < ε := by
    have hmono := mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ 2 - ε₀ by linarith)
    nlinarith only [hmono, hlose]
  have hsmall := (hcont.continuousAt.tendsto.comp hqLimit).eventually (gt_mem_nhds hqsmall)
  filter_upwards [hX.eventually (hcoeff N), hX.eventually hpos, hpos,
    eventually_ge_atTop (1 : ℝ), hsmall,
    eventual_time_budget S hB hdimension hC hr hα hη hpower hN hNε]
    with T hcoeffT hWX hWT hT hsmallT htime
  refine ⟨hWT, ?_⟩
  intro a
  have hXT : T ^ α ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (hαmin.trans_le (min_le_right _ _)).le
  obtain ⟨u, hu, hloss⟩ := cutoff_recurrence S w hw hC hr hcoeffT hN hNε hWX htime a
  exact ⟨u, hu, (tail_loss_bound S w hw hXT hWX hWT hloss).trans hsmallT⟩

end D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
