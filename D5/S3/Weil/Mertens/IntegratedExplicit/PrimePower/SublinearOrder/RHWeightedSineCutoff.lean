/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Effective linear independence gives a window bound for the actual weighted zeta sine sum. -/

import D5.S3.Fourier.WeightedPhaseRecurrence
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootWeightedSine
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative recurrence for the harmonic-multiplicity sine polynomial of the zeta zeros. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedSineCutoff

open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Fourier.WeightedPhaseRecurrence (phaseLoss weighted_phase_recurrence)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)

private theorem mem_cut {S : Spectrum} {X : ℝ} {j : S.index} :
    j ∈ S.cut X ↔ S.gamma j ≤ X :=
  (S.finite_le X).mem_toFinset

private def ordinateEmbedding (hRH : RiemannHypothesis) :
    (zetaSpectrum hRH).index ↪ ℝ :=
  ⟨(zetaSpectrum hRH).gamma, (zetaSpectrum hRH).gamma_injective⟩

/-- The distinct positive zeta ordinates through the inclusive cutoff. -/
def positiveOrdinates (hRH : RiemannHypothesis) (X : ℝ) : Finset ℝ :=
  ((zetaSpectrum hRH).cut X).map (ordinateEmbedding hRH)

/-- Lamzouri's Conjecture 1.1 on the positive ordinate set. The count bound
uses the analytic multiplicities in the canonical window `(0, X]`. -/
def EffectiveLI (hRH : RiemannHypothesis) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
    ∀ X : ℝ, 2 ≤ X → ∀ k : positiveOrdinates hRH X → ℤ,
      (∃ j, k j ≠ 0) → (∀ j, |k j| ≤ (Zeta23.zetaZeroConfig.N 0 X : ℤ)) →
      C * Real.exp (-(X ^ (1 + η))) ≤ |∑ j, (k j : ℝ) * (j : ℝ)|

private theorem cut_card_le_count (hRH : RiemannHypothesis) (X : ℝ) :
    (positiveCutoff hRH X).card ≤ (zetaSpectrum hRH).N X := by
  classical
  let S := zetaSpectrum hRH
  change (S.cut X).card ≤ S.N X
  calc
    (S.cut X).card = ∑ _j ∈ S.cut X, 1 := by simp
    _ ≤ S.N X := Finset.sum_le_sum (fun j _ => S.mult_pos j)

/-- The recurrence budget eventually holds at the power cutoff. -/
private theorem eventual_time_budget (hRH : RiemannHypothesis)
    {C r α β η ε₀ : ℝ} {N : ℕ}
    (hC : 0 < C) (hr : 0 < r) (hα : 0 < α) (hη : 0 < η)
    (hpower : α * (1 + η) < β) (hN : 0 < N) (hε : 1 / (N : ℝ) < ε₀) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (T ^ β) * (C * Real.exp (-((T ^ α) ^ (1 + η))) / r) *
          (ε₀ - 1 / (N : ℝ)) >
        2 * (ε₀ * (N : ℝ) ^ (positiveCutoff hRH (T ^ α)).card -
          (ε₀ - 1 / (N : ℝ))) := by
  obtain ⟨B, hB, hcount⟩ := count_upper _ (zetaSpectrum_countAsymptotic hRH)
  have hd : ∀ᶠ X : ℝ in atTop, ((positiveCutoff hRH X).card : ℝ) ≤ B * (X * Real.log X) := by
    filter_upwards [hcount] with X hX
    exact (Nat.cast_le.mpr (cut_card_le_count hRH X)).trans hX
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
  have hdim : ((positiveCutoff hRH (T ^ α)).card : ℝ) * Real.log (N : ℝ) ≤
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
      Real.log K + ((positiveCutoff hRH (T ^ α)).card : ℝ) * Real.log (N : ℝ) <
        T ^ β - (T ^ α) ^ (1 + η) := by
    rw [hpow]
    linarith
  have hexp := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_add, Real.exp_log hK, Real.exp_nat_mul,
    Real.exp_log (zero_lt_one.trans_le hNreal), Real.exp_sub] at hexp
  have hscaled := mul_lt_mul_of_pos_left hexp (show 0 < C * (ε₀ - 1 / (N : ℝ)) / r
    from div_pos (mul_pos hC hgap) hr)
  have heq : (C * (ε₀ - 1 / (N : ℝ)) / r) * (K * (N : ℝ) ^ (positiveCutoff hRH (T ^ α)).card) =
      2 * (ε₀ * (N : ℝ) ^ (positiveCutoff hRH (T ^ α)).card) := by
    change (C * (ε₀ - 1 / (N : ℝ)) / r) *
      (2 * ε₀ * r / (C * (ε₀ - 1 / (N : ℝ))) * (N : ℝ) ^ (positiveCutoff hRH (T ^ α)).card) = _
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

private theorem count_tendsto (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => ((zetaSpectrum hRH).N T : ℝ)) atTop atTop := by
  have hS := zetaSpectrum_countAsymptotic hRH
  have hlog : Tendsto (fun T : ℝ => T * Real.log T) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  apply ((hS.pos_mul_atTop (show (0 : ℝ) < 1 / (2 * Real.pi) by positivity)) hlog).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact div_mul_cancel₀ _ (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)).ne'

private theorem harmonic_eventually_pos (hRH : RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop, 0 < harmonicMass hRH T := by
  have hc : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
  filter_upwards [(harmonic_mass_limit hRH).eventually (lt_mem_nhds hc)]
    with T hT
  exact ((div_pos_iff.mp hT).resolve_right (fun h => (not_lt_of_ge (sq_nonneg _)) h.2)).1

private theorem harmonic_ratio (hRH : RiemannHypothesis) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun T : ℝ =>
      harmonicMass hRH (T ^ α) / harmonicMass hRH T)
        atTop (nhds (α ^ 2)) := by
  let W := harmonicMass hRH
  let c : ℝ := 1 / (4 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : Tendsto (fun T : ℝ => W T / (Real.log T)^2) atTop (nhds c) :=
    harmonic_mass_limit hRH
  have hratio := ((hm.comp (tendsto_rpow_atTop hα)).div hm hc.ne').const_mul (α ^ 2)
  rw [div_self hc.ne', mul_one] at hratio
  apply hratio.congr'
  filter_upwards [harmonic_eventually_pos hRH, eventually_gt_atTop (1 : ℝ)] with T hWT hT
  have hl := Real.log_pos hT
  have hlog : Real.log (T ^ α) = α * Real.log T :=
    Real.log_rpow (zero_lt_one.trans hT) _
  change α ^ 2 * (W (T ^ α) / (Real.log (T ^ α)) ^ 2 / (W T / (Real.log T)^2)) = _
  change 0 < W T at hWT
  change _ = W (T ^ α) / W T
  rw [hlog]
  field_simp [hl.ne', hα.ne', ne_of_gt hWT]

private theorem harmonicWeight_nonneg (j : PositiveZetaZero) : 0 ≤ harmonicWeight j := by
  have hj : 0 < ordinate j := j.property.2
  unfold harmonicWeight
  positivity

private theorem tail_loss_bound (hRH : RiemannHypothesis) {X T : ℝ} (hXT : X ≤ T)
    (hWX : 0 < harmonicMass hRH X) (hWT : 0 < harmonicMass hRH T) {v ε₀ : ℝ}
    (hsmall : 1 - weightedSine hRH X v / harmonicMass hRH X < ε₀) :
    1 - weightedSine hRH T v / harmonicMass hRH T <
      2 * (1 - harmonicMass hRH X / harmonicMass hRH T) +
        (harmonicMass hRH X / harmonicMass hRH T) * ε₀ := by
  classical
  let f (j : PositiveZetaZero) : ℝ := harmonicWeight j * Real.sin (ordinate j * v)
  have hsub : positiveCutoff hRH X ⊆ positiveCutoff hRH T :=
    fun _ hj => mem_cut.mpr ((mem_cut.mp hj).trans hXT)
  have hW := Finset.sum_sdiff (f := harmonicWeight) hsub
  have hF := Finset.sum_sdiff (f := f) hsub
  change (∑ j ∈ positiveCutoff hRH T \ positiveCutoff hRH X, harmonicWeight j) +
    harmonicMass hRH X = harmonicMass hRH T at hW
  change (∑ j ∈ positiveCutoff hRH T \ positiveCutoff hRH X, f j) +
    weightedSine hRH X v = weightedSine hRH T v at hF
  have hn : -(∑ j ∈ positiveCutoff hRH T \ positiveCutoff hRH X, harmonicWeight j) ≤
      ∑ j ∈ positiveCutoff hRH T \ positiveCutoff hRH X, f j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    simpa only [f, mul_neg, mul_one] using
      mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (ordinate j * v))
        (harmonicWeight_nonneg j)
  have hsmall' := (div_lt_iff₀ hWX).mp (show
      (harmonicMass hRH X - weightedSine hRH X v) / harmonicMass hRH X < ε₀ by
    rwa [sub_div, div_self hWX.ne'])
  have hfull : harmonicMass hRH T - weightedSine hRH T v <
      2 * (harmonicMass hRH T - harmonicMass hRH X) + harmonicMass hRH X * ε₀ := by
    linarith only [hW, hF, hn, hsmall']
  have hdiv := div_lt_div_of_pos_right hfull hWT
  rw [sub_div, div_self hWT.ne'] at hdiv
  convert hdiv using 1
  field_simp [hWT.ne']

private theorem choose_cutoff_parameters {β ε : ℝ} (hβ : 0 < β)
    (hε : 2 * (1 - (min β 1)^2) < ε) :
    ∃ α η ε₀ : ℝ, 0 < α ∧ α < min β 1 ∧ 0 < η ∧ α * (1 + η) < β ∧
      0 < ε₀ ∧ 2 * (1 - α^2) + α^2 * ε₀ < ε := by
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
  refine ⟨α, z - 1, (ε - 2 * (1 - α^2)) / 2, hα, hαm, sub_pos.mpr hz₁, ?_, ?_, ?_⟩
  · have hz := (lt_div_iff₀ hα).mp hz₂
    linarith only [hz, show α * (1 + (z - 1)) = z * α by ring]
  · positivity
  · have hαsq : α^2 ≤ 1 := by nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hαone.le)]
    have hm := mul_le_mul_of_nonneg_right hαsq
      (show 0 ≤ (ε - 2 * (1 - α^2)) / 2 by positivity)
    linarith

private theorem cutoff_recurrence (hRH : RiemannHypothesis)
    {η C r X ε₀ R : ℝ} {N : ℕ} (hC : 0 < C) (hr : 0 < r)
    (hcoeff : ∀ k : positiveOrdinates hRH X → ℤ,
      (∃ j, k j ≠ 0) → (∀ j, |k j| ≤ (Zeta23.zetaZeroConfig.N 0 X : ℤ)) →
      C * Real.exp (-(X ^ (1 + η))) ≤ |∑ j, (k j : ℝ) * (j : ℝ)|)
    (hN : 0 < N) (hcount : N ≤ (zetaSpectrum hRH).N X)
    (hε : 1 / (N : ℝ) < ε₀) (hW : 0 < harmonicMass hRH X)
    (hR : R * (C * Real.exp (-(X ^ (1 + η))) / r) * (ε₀ - 1 / (N : ℝ)) >
      2 * (ε₀ * (N : ℝ) ^ (positiveCutoff hRH X).card - (ε₀ - 1 / (N : ℝ)))) :
    ∀ a : ℝ, ∃ u ∈ Icc a (a + R),
      1 - weightedSine hRH X (u / r) / harmonicMass hRH X < ε₀ := by
  classical
  let K := positiveCutoff hRH X
  let eγ : K ≃ positiveOrdinates hRH X := K.equivMap (ordinateEmbedding hRH)
  let p : K → ℝ := fun j => harmonicWeight j.val / harmonicMass hRH X
  let g : K → ℝ := fun j => ordinate j.val / r
  let θ : K → ℝ := fun _ => Real.pi / 2
  let δ := C * Real.exp (-(X ^ (1 + η))) / r
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hp (j : K) : 0 ≤ p j := div_nonneg (harmonicWeight_nonneg j.val) hW.le
  have hp1 : ∑ j : K, p j = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div, Finset.sum_coe_sort, ← show harmonicMass hRH X =
      ∑ j ∈ K, harmonicWeight j from rfl, div_self hW.ne']
  have hN' : (N : ℤ) ≤ (Zeta23.zetaZeroConfig.N 0 X : ℤ) := by
    rw [zetaSpectrum_N hRH X] at hcount
    exact_mod_cast hcount
  have hmodes (k : K → ℤ) (hk : ∀ j, |k j| ≤ (N : ℤ)) (hnz : ∃ j, k j ≠ 0) :
      δ ≤ |∑ j, (k j : ℝ) * g j| := by
    let ℓ : positiveOrdinates hRH X → ℤ := fun j => k (eγ.symm j)
    have hℓ : ∃ j, ℓ j ≠ 0 := by
      obtain ⟨i, hi⟩ := hnz
      exact ⟨eγ i, by simpa [ℓ] using hi⟩
    have hbound := hcoeff ℓ hℓ (fun j => (hk (eγ.symm j)).trans hN')
    have htransport : (∑ j, (ℓ j : ℝ) * (j : ℝ)) = r * (∑ i, (k i : ℝ) * g i) := by
      rw [Finset.mul_sum]
      symm
      apply Fintype.sum_equiv eγ
      intro j
      have heq : ((eγ j : positiveOrdinates hRH X) : ℝ) = ordinate j.val := rfl
      simp only [ℓ, Equiv.symm_apply_apply, heq, g]
      field_simp [hr.ne']
    rw [htransport, abs_mul, abs_of_pos hr] at hbound
    exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hbound)
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
      weightedSine hRH X (u / r) / harmonicMass hRH X := by
    calc
      _ = ∑ j : K,
          (harmonicWeight j.val * Real.sin (ordinate j.val * (u / r))) / harmonicMass hRH X := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show θ j = Real.pi / 2 from rfl, Real.cos_sub_pi_div_two,
          show g j * u = ordinate j.val * (u / r) by dsimp only [g]; ring]
        dsimp only [p]
        ring
      _ = _ := by
        rw [← Finset.sum_div,
          Finset.sum_coe_sort K (fun j => harmonicWeight j * Real.sin (ordinate j * (u / r)))]
        rfl
  simp only [phaseLoss, mul_sub, mul_one, Finset.sum_sub_distrib, hp1, hscore] at hloss
  exact ⟨u, hu, hloss⟩

/-- Under RH and Effective LI, the actual weighted sine sum attains the cutoff loss
bound in every interval of the prescribed length at sufficiently large cutoffs. -/
theorem eventual_weighted_sine_cutoff_tradeoff
    (hRH : RiemannHypothesis) (hELI : EffectiveLI hRH) {r β ε : ℝ} (hr : 0 < r) (hβ : 0 < β)
    (hε : 2 * (1 - (min β 1)^2) < ε) :
    ∀ᶠ T : ℝ in atTop, 0 < harmonicMass hRH T ∧
      ∀ a : ℝ, ∃ u ∈ Icc a (a + Real.exp (T ^ β)),
        1 - weightedSine hRH T (u / r) / harmonicMass hRH T < ε := by
  obtain ⟨α, η, ε₀, hα, hαmin, hη, hpower, hε₀, hlose⟩ := choose_cutoff_parameters hβ hε
  obtain ⟨N, hNbig⟩ := exists_nat_gt (1 / ε₀)
  have hNreal : (0 : ℝ) < N := (by positivity : 0 < 1 / ε₀).trans hNbig
  have hN : 0 < N := by exact_mod_cast hNreal
  have hNε : 1 / (N : ℝ) < ε₀ := by
    apply (div_lt_iff₀ hNreal).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε₀).mp hNbig
  obtain ⟨C, hC, hELI⟩ := hELI η hη
  have hX := tendsto_rpow_atTop hα
  have hcount := (count_tendsto hRH).eventually_ge_atTop (N : ℝ)
  have hratio := harmonic_ratio hRH hα
  have hcont : Continuous (fun q : ℝ => 2 * (1 - q) + q * ε₀) := by fun_prop
  have hsmall := (hcont.continuousAt.tendsto.comp hratio).eventually (gt_mem_nhds hlose)
  filter_upwards [hX.eventually (eventually_ge_atTop (2 : ℝ)),
    hX.eventually hcount, hX.eventually (harmonic_eventually_pos hRH),
    harmonic_eventually_pos hRH, eventually_ge_atTop (1 : ℝ), hsmall,
    eventual_time_budget hRH hC hr hα hη hpower hN hNε] with T hT2 hcountT hWX hWT hT hsmallT htime
  refine ⟨hWT, ?_⟩
  intro a
  have hXT : T ^ α ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (hαmin.trans_le (min_le_right _ _)).le
  obtain ⟨u, hu, hloss⟩ := cutoff_recurrence hRH hC hr (hELI (T ^ α) hT2)
    hN (by exact_mod_cast hcountT) hNε hWX htime a
  exact ⟨u, hu, (tail_loss_bound hRH hXT hWX hWT hloss).trans hsmallT⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedSineCutoff
