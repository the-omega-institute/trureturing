/- GID: D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper
   generality: G
   mirror-B: D5/B/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise deterministic recovery of the ground energy of finite atomic laws. -/

import D5.S3.Analytic.Interpolation.UniformCoefficientBudget
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Set MeasureTheory
open Finset (range mem_range)
open scoped ENNReal
open D5.S3.Analytic.Interpolation.UniformCoefficientBudget
namespace D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper

/-- Finite Borel probability laws; only the ground atom has a prescribed mass. -/
def AtomicLaw (Elo Ehi η : ℝ) (d : ℕ) (μ : Measure ℝ) (g : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ENNReal.ofReal η ≤ μ {g} ∧
    ∃ s : Finset ℝ, (s : Set ℝ) = μ.support ∧ s.card ≤ d ∧ g ∈ s ∧
      ∀ x ∈ s, x ∈ Icc Elo Ehi ∧ g ≤ x

/-- The original measure-valued Laplace observation. -/
def measureCurve (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (-t * x) ∂μ

/-- The all-time dimension and precision rate. -/
def rateAll (d : ℕ) (ε : ℝ) : ℝ :=
  sSup ((fun m : ℕ => Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) / (m : ℝ) ^ 2) ''
    (Set.Icc 1 d : Set ℕ))

/-- The finite window rate, including saturation at the geometric bound. -/
def rateWindow (d : ℕ) (ε U : ℝ) : ℝ :=
  sSup ((fun m : ℕ => min (1 : ℝ)
    (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) * max 1 (((2 * m - 1 : ℕ) : ℝ) / U)) /
      (m : ℝ) ^ 2) '' (Set.Icc 1 d : Set ℕ))

/-- Complete lattice minimax risk; observations are arbitrary pointwise functions. -/
def minimaxRisk (Elo Ehi η : ℝ) (d : ℕ) (D : Set ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ G : (D → ℝ) → ℝ, ⨆ μ : Measure ℝ, ⨆ g : ℝ,
    ⨆ (_ : AtomicLaw Elo Ehi η d μ g), ⨆ Y : D → ℝ,
      ⨆ (_ : ∀ t : D, |Y t - measureCurve μ t| ≤ ε), ENNReal.ofReal |G Y - g|

/-- The measure model has an exact finite weight representation, preserving its curve. -/
theorem atomic_law_representation {Elo Ehi η : ℝ} {d : ℕ} {μ : Measure ℝ} {g : ℝ}
    (h : AtomicLaw Elo Ehi η d μ g) :
    g ∈ Icc Elo Ehi ∧ ∃ w : ℝ →₀ ℝ,
      (∀ x, 0 ≤ w x) ∧ w.sum (fun _ a => a) = 1 ∧
      (∀ x ∈ w.support, x ∈ Icc g Ehi) ∧ η ≤ w g ∧ w.support.card ≤ d ∧
      μ = ∑ x ∈ w.support, ENNReal.ofReal (w x) • Measure.dirac x ∧
      ∀ t, measureCurve μ t = atomicLaplace w t := by
  classical
  rcases h with ⟨hprob, hmass, s, hsupport, hcard, hg, hs⟩
  have hnull : μ ((s : Set ℝ)ᶜ) = 0 := by
    rw [hsupport]
    exact Measure.measure_compl_support
  haveI : IsProbabilityMeasure μ := hprob
  have hzero (x : ℝ) (hx : x ∉ s) : μ {x} = 0 :=
    measure_mono_null (by simpa using hx : ({x} : Set ℝ) ⊆ (s : Set ℝ)ᶜ) hnull
  let w : ℝ →₀ ℝ := Finsupp.onFinset s (fun x => (μ {x}).toReal)
    (fun x hx => by by_contra hn; exact hx (by rw [hzero x hn]; simp))
  have hw (x : ℝ) : w x = (μ {x}).toReal := Finsupp.onFinset_apply
  have hsub : w.support ⊆ s := Finsupp.support_onFinset_subset
  have hrep : μ = ∑ x ∈ s, μ {x} • Measure.dirac x :=
    Measure.ae_mem_finset_iff.mp (by simpa only [ae_iff, Set.compl_def, Finset.mem_coe] using hnull)
  have hsum : ∑ x ∈ s, μ {x} = 1 := by
    have hh := congrArg (fun v : Measure ℝ => v Set.univ) hrep
    simpa using hh.symm
  have htotal : w.sum (fun _ a => a) = 1 := by
    rw [Finsupp.sum_of_support_subset w hsub _ (by simp)]
    simp only [hw]
    rw [← ENNReal.toReal_sum (fun x _ => measure_ne_top μ {x}), hsum]
    simp
  have hwrep : μ = ∑ x ∈ w.support, ENNReal.ofReal (w x) • Measure.dirac x := by
    rw [hrep]
    simp only [hw, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : w x = 0 := Finsupp.notMem_support_iff.mp hnx
    have hmz : μ {x} = 0 := by
      have := congrArg ENNReal.ofReal (hw x)
      simpa [hz, ENNReal.ofReal_toReal (measure_ne_top μ {x})] using this.symm
    simp [hmz]
  refine ⟨(hs g hg).1, w, (fun x => hw x ▸ ENNReal.toReal_nonneg), htotal,
    (fun x hx => ⟨(hs x (hsub hx)).2, (hs x (hsub hx)).1.2⟩), ?_,
    (Finset.card_le_card hsub).trans hcard, hwrep, ?_⟩
  · rw [hw]
    exact ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ {g}) |>.mp hmass
  · intro t
    rw [measureCurve, hwrep, integral_finsetSum_measure]
    · simp only [integral_smul_measure, integral_dirac, hw,
        ENNReal.ofReal_toReal (measure_ne_top μ _), smul_eq_mul]
      rfl
    · intro x hx
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma rate_all_term_le (d m : ℕ) (ε : ℝ) (hm : m ∈ Set.Icc 1 d) :
    Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) / (m : ℝ) ^ 2 ≤ rateAll d ε :=
  le_csSup ((Set.finite_Icc 1 d).image _).bddAbove ⟨m, hm, rfl⟩

private lemma rate_window_term_le (d m : ℕ) (ε U : ℝ) (hm : m ∈ Set.Icc 1 d) :
    min 1 (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) *
      max 1 (((2 * m - 1 : ℕ) : ℝ) / U)) / (m : ℝ) ^ 2 ≤ rateWindow d ε U :=
  le_csSup ((Set.finite_Icc 1 d).image _).bddAbove ⟨m, hm, rfl⟩

private lemma rate_all_nonneg (d : ℕ) (ε : ℝ) (hd : 1 ≤ d) (hε : 0 ≤ ε) :
    0 ≤ rateAll d ε :=
  (div_nonneg (Real.rpow_nonneg hε _) (sq_nonneg _)).trans
    (rate_all_term_le d 1 ε ⟨le_rfl, hd⟩)

private lemma rate_window_nonneg (d : ℕ) (ε U : ℝ) (hd : 1 ≤ d) (hε : 0 ≤ ε) :
    0 ≤ rateWindow d ε U :=
  (div_nonneg (le_min zero_le_one (mul_nonneg (Real.rpow_nonneg hε _)
    (zero_le_one.trans (le_max_left _ _)))) (sq_nonneg _)).trans
    (rate_window_term_le d 1 ε U ⟨le_rfl, hd⟩)

private lemma midpoint_error (S : Set ℝ) (x R : ℝ) (hx : x ∈ S)
    (hb : BddBelow S) (ha : BddAbove S)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ 2 * R) :
    |(sInf S + sSup S) / 2 - x| ≤ R := by
  have hinf : sInf S ≤ x := csInf_le hb hx
  have hsup : x ≤ sSup S := le_csSup ha hx
  have hwidth : sSup S - 2 * R ≤ sInf S := by
    apply le_csInf ⟨x, hx⟩
    intro b hb'
    have hh : sSup S ≤ b + 2 * R := by
      apply csSup_le ⟨x, hx⟩
      intro a ha'
      have := (le_abs_self (a - b)).trans (hdiam a ha' b hb')
      linarith
    linarith
  apply abs_le.mpr
  constructor <;> linarith

/-- Spectral endpoints consistent with one arbitrary pointwise observation. -/
def compatibleGrounds (Elo Ehi η : ℝ) (d : ℕ) (D : Set ℝ) (ε : ℝ) (Y : D → ℝ) :
    Set ℝ := {g | ∃ μ : Measure ℝ, AtomicLaw Elo Ehi η d μ g ∧
      ∀ t : D, |Y t - measureCurve μ t| ≤ ε}

/-- The compatible endpoint midpoint; empty data fibers receive the lower endpoint. -/
def midpointEstimator (Elo Ehi η : ℝ) (d : ℕ) (D : Set ℝ) (ε : ℝ) : (D → ℝ) → ℝ :=
  by
  classical
  exact fun Y => if (compatibleGrounds Elo Ehi η d D ε Y).Nonempty then
    (sInf (compatibleGrounds Elo Ehi η d D ε Y) +
      sSup (compatibleGrounds Elo Ehi η d D ε Y)) / 2 else Elo

private lemma midpoint_estimator_bound (Elo Ehi η ε R : ℝ) (d : ℕ) (D : Set ℝ)
    (hdiam : ∀ (μ ν : Measure ℝ) (gμ gν : ℝ),
      AtomicLaw Elo Ehi η d μ gμ → AtomicLaw Elo Ehi η d ν gν →
      (∀ t ∈ D, |measureCurve μ t - measureCurve ν t| ≤ 2 * ε) → |gμ - gν| ≤ 2 * R)
    (μ : Measure ℝ) (g : ℝ) (hμ : AtomicLaw Elo Ehi η d μ g) (Y : D → ℝ)
    (hY : ∀ t : D, |Y t - measureCurve μ t| ≤ ε) :
    |midpointEstimator Elo Ehi η d D ε Y - g| ≤ R := by
  let S := compatibleGrounds Elo Ehi η d D ε Y
  have hg : g ∈ S := ⟨μ, hμ, hY⟩
  have hb : S ⊆ Icc Elo Ehi := by
    intro x hx
    rcases hx with ⟨ν, hν, _⟩
    rcases hν.2.2 with ⟨s, _, _, hxs, hs⟩
    exact (hs x hxs).1
  rw [midpointEstimator, if_pos ⟨g, hg⟩]
  apply midpoint_error S g R hg
    ⟨Elo, fun x hx => (hb hx).1⟩ ⟨Ehi, fun x hx => (hb hx).2⟩
  intro a ha b hb'
  rcases ha with ⟨ν, hν, hνY⟩
  rcases hb' with ⟨κ, hκ, hκY⟩
  apply hdiam ν κ a b hν hκ
  intro t ht
  have h1 := hνY ⟨t, ht⟩
  have h2 := hκY ⟨t, ht⟩
  have hh := abs_sub_le (measureCurve ν t) (Y ⟨t, ht⟩) (measureCurve κ t)
  rw [abs_sub_comm (measureCurve ν t) (Y ⟨t, ht⟩)] at hh
  linarith

private lemma minimax_of_estimator (Elo Ehi η ε R : ℝ) (d : ℕ) (D : Set ℝ)
    (G : (D → ℝ) → ℝ)
    (hG : ∀ (μ : Measure ℝ) (g : ℝ), AtomicLaw Elo Ehi η d μ g →
      ∀ Y : D → ℝ, (∀ t : D, |Y t - measureCurve μ t| ≤ ε) → |G Y - g| ≤ R) :
    minimaxRisk Elo Ehi η d D ε ≤ ENNReal.ofReal R := by
  apply (iInf_le _ G).trans
  refine iSup_le fun μ => iSup_le fun g => iSup_le fun hμ =>
    iSup_le fun Y => iSup_le fun hY => ?_
  exact ENNReal.ofReal_le_ofReal (hG μ g hμ Y hY)

private lemma certificate_noise (s : Finset ℕ) (c a b : ℕ → ℝ) (ε : ℝ)
    (hnoise : ∀ k ∈ s, |a k - b k| ≤ 2 * ε)
    (hsep : 1 ≤ ∑ k ∈ s, c k * (a k - b k)) :
    1 ≤ 2 * ε * ∑ k ∈ s, |c k| := by
  calc
    1 ≤ ∑ k ∈ s, c k * (a k - b k) := hsep
    _ ≤ ∑ k ∈ s, |c k| * (2 * ε) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hnoise k hk) (abs_nonneg _)
    _ = 2 * ε * ∑ k ∈ s, |c k| := by rw [← Finset.sum_mul]; ring

private lemma gap_of_certificate (η Δ ε M : ℝ) (m : ℕ)
    (hη : 0 < η) (hΔ : 0 < Δ) (hε : 0 < ε) (hM : 0 < M) (hm : 0 < m)
    (hcert : 1 ≤ 2 * ε * (1024 * M / (η ^ 2 * (m : ℝ) ^ 2 * Δ)) ^ (2 * m - 1)) :
    Δ ≤ 2 * (1024 / η ^ 2) *
      (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) * M) / (m : ℝ) ^ 2 := by
  let q := 2 * m - 1
  have hq : 0 < q := by dsimp [q]; omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let B := 1024 * M / (η ^ 2 * (m : ℝ) ^ 2 * Δ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hh : 1 / (2 * ε) ≤ B ^ q := (div_le_iff₀ (by positivity)).mpr (by
    simpa [q, B, mul_comm] using hcert)
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / (2 * ε)) hh
    (by positivity : 0 ≤ (q : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hB.le (Nat.ne_of_gt hq), Real.div_rpow zero_le_one (by positivity),
    Real.one_rpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le] at hr
  have htwo : Real.rpow 2 ((q : ℝ)⁻¹) ≤ 2 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (inv_le_one_of_one_le₀ hqR) using 1 <;> simp
  have hr' : Δ ≤ Real.rpow 2 ((q : ℝ)⁻¹) * Real.rpow ε ((q : ℝ)⁻¹) *
      (1024 * M / (η ^ 2 * (m : ℝ) ^ 2)) := by
    dsimp [B] at hr
    have hroot : 0 < Real.rpow 2 ((q : ℝ)⁻¹) * Real.rpow ε ((q : ℝ)⁻¹) :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hε _)
    have hn := (div_le_div_iff₀ (by exact hroot :
      0 < Real.rpow 2 ((q : ℝ)⁻¹) * Real.rpow ε ((q : ℝ)⁻¹))
      (by positivity : 0 < η ^ 2 * (m : ℝ) ^ 2 * Δ)).mp hr
    have hn' : Δ * (η ^ 2 * (m : ℝ) ^ 2) ≤
        Real.rpow 2 ((q : ℝ)⁻¹) * Real.rpow ε ((q : ℝ)⁻¹) * (1024 * M) := by
      calc
        Δ * (η ^ 2 * (m : ℝ) ^ 2) = 1 * (η ^ 2 * (m : ℝ) ^ 2 * Δ) := by ring
        _ ≤ 1024 * M * (Real.rpow 2 ((q : ℝ)⁻¹) * Real.rpow ε ((q : ℝ)⁻¹)) := hn
        _ = _ := by ring
    have hout := (le_div_iff₀ (by positivity : 0 < η ^ 2 * (m : ℝ) ^ 2)).mpr hn'
    calc
      Δ ≤ _ := hout
      _ = _ := by ring
  calc
    Δ ≤ _ := hr'
    _ ≤ 2 * Real.rpow ε ((q : ℝ)⁻¹) * (1024 * M / (η ^ 2 * (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hε.le _)) (by positivity)
    _ = _ := by dsimp [q]; ring

private lemma truncated_gap (η Δ ε M : ℝ) (m : ℕ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hM : 0 < M) (hm : 0 < m) (hgeom : (m : ℝ) ^ 2 * Δ ≤ 16 / η)
    (hcert : 1 ≤ 2 * ε * (1024 * M / (η ^ 2 * (m : ℝ) ^ 2 * Δ)) ^ (2 * m - 1)) :
    Δ ≤ 2 * (1024 / η ^ 2) *
      min 1 (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) * M) / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hg := (le_div_iff₀ hη).mp hgeom
  have hg' := mul_le_mul_of_nonneg_right hg hη.le
  have hcoarse : Δ ≤ 2 * (1024 / η ^ 2) / (m : ℝ) ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < (m : ℝ) ^ 2)).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < η ^ 2)).mpr
    calc
      Δ * (m : ℝ) ^ 2 * η ^ 2 = (m : ℝ) ^ 2 * Δ * η * η := by ring
      _ ≤ 16 * η := hg'
      _ ≤ 16 := by linarith only [hη1]
      _ ≤ 2 * 1024 := by norm_num
  rcases le_total 1 (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) * M) with ht | ht
  · simpa only [min_eq_left ht, mul_one] using hcoarse
  · simpa only [min_eq_right ht] using gap_of_certificate η Δ ε M m hη hΔ hε hM hm hcert

private lemma measure_joint_certificates {Elo E η : ℝ} {d : ℕ}
    (hElo : 0 ≤ Elo) (hE : 0 < E) (hη : 0 < η) (hη1 : η ≤ 1) (hd : 0 < d)
    (μ ν : Measure ℝ) (gμ gν : ℝ)
    (hμ : AtomicLaw Elo E η d μ gμ) (hν : AtomicLaw Elo E η d ν gν)
    (hne : gμ ≠ gν) :
    let Δ := |gμ - gν| / E
    ∃ m : ℕ, 0 < m ∧ m ≤ d ∧ (m : ℝ) ^ 2 * Δ ≤ 16 / η ∧
      (∃ c : ℕ → ℝ,
        1 ≤ ∑ k ∈ range (2 * m), c k *
          (measureCurve μ ((k : ℝ) / E) - measureCurve ν ((k : ℝ) / E)) ∧
        (∑ k ∈ range (2 * m), |c k|) ≤ (1024 / (η ^ 2 * (m : ℝ) ^ 2 * Δ)) ^ (2 * m - 1)) ∧
      (∀ U : ℝ, 0 < U →
        let M := max 1 (((2 * m - 1 : ℕ) : ℝ) / U)
        ∃ c : ℕ → ℝ,
          (∀ k < 2 * m, (k : ℝ) * (1 / (M * E)) ∈ Icc 0 (U / E)) ∧
          1 ≤ ∑ k ∈ range (2 * m), c k *
            (measureCurve μ ((k : ℝ) * (1 / (M * E))) -
              measureCurve ν ((k : ℝ) * (1 / (M * E)))) ∧
          (∑ k ∈ range (2 * m), |c k|) ≤
            (1024 * M / (η ^ 2 * (m : ℝ) ^ 2 * Δ)) ^ (2 * m - 1)) := by
  obtain ⟨hgμ, wμ, hwμ, htμ, hsμ, hmμ, hcμ, _, hcurveμ⟩ := atomic_law_representation hμ
  obtain ⟨hgν, wν, hwν, htν, hsν, hmν, hcν, _, hcurveν⟩ := atomic_law_representation hν
  have hc := laplace_joint_certificates wμ wν η E gμ gν d hd hE hη hη1
    ⟨hElo.trans hgμ.1, hgμ.2⟩ ⟨hElo.trans hgν.1, hgν.2⟩ hne
    hwμ hwν htμ htν hsμ hsν hmμ hmν hcμ hcν
  dsimp only at hc ⊢
  let m := min d ⌈3 / Real.sqrt (η * (|gμ - gν| / E))⌉₊
  obtain ⟨hm, hmd, hgeom, hall, hwin⟩ := hc
  have hq : 2 * m - 1 + 1 = 2 * m := by omega
  dsimp only [m] at hq
  refine ⟨m, hm, hmd, hgeom, ?_, ?_⟩
  · simpa only [m, ← hcurveμ, ← hcurveν, hq] using (show ∃ c : ℕ → ℝ,
      1 ≤ ∑ k ∈ range (2 * m - 1 + 1), c k *
        (atomicLaplace wμ ((k : ℝ) / E) - atomicLaplace wν ((k : ℝ) / E)) ∧
      (∑ k ∈ range (2 * m - 1 + 1), |c k|) ≤
        (1024 / (η ^ 2 * (m : ℝ) ^ 2 * (|gμ - gν| / E))) ^ (2 * m - 1) from hall)
  · intro U hU
    obtain ⟨c, htime, hsep, hnorm⟩ := hwin U hU
    refine ⟨c, (fun k hk => htime k (by omega)), ?_, ?_⟩
    · simpa only [m, ← hcurveμ, ← hcurveν, hq] using hsep
    · simpa only [m, hq] using hnorm

private lemma all_diameter (Elo E η ε : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : 0 < E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hd : 1 ≤ d) (hε : 0 < ε)
    (μ ν : Measure ℝ) (gμ gν : ℝ)
    (hμ : AtomicLaw Elo E η d μ gμ) (hν : AtomicLaw Elo E η d ν gν)
    (hnoise : ∀ t ∈ Ici 0, |measureCurve μ t - measureCurve ν t| ≤ 2 * ε) :
    |gμ - gν| ≤ 2 * ((1024 * E / η ^ 2) * rateAll d ε) := by
  by_cases heq : gμ = gν
  · simp only [heq, sub_self, abs_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg (by positivity) (rate_all_nonneg d ε hd hε.le))
  obtain ⟨m, hm, hmd, _, ⟨c, hsep, hnorm⟩, _⟩ :=
    measure_joint_certificates hElo hE hη hη1 (by omega) μ ν gμ gν hμ hν heq
  have hΔ : 0 < |gμ - gν| / E := div_pos (abs_pos.mpr (sub_ne_zero.mpr heq)) hE
  have hn := certificate_noise (range (2 * m)) c
    (fun k => measureCurve μ ((k : ℝ) / E)) (fun k => measureCurve ν ((k : ℝ) / E))
    ε (fun k _ => hnoise _ (by change 0 ≤ (k : ℝ) / E; positivity)) hsep
  have hcert := hn.trans (mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 2 * ε))
  have hgap := gap_of_certificate η (|gμ - gν| / E) ε 1 m hη hΔ hε zero_lt_one hm
    (by simpa only [mul_one] using hcert)
  have hr := rate_all_term_le d m ε ⟨hm, hmd⟩
  have hh : |gμ - gν| / E ≤ 2 * (1024 / η ^ 2) * rateAll d ε := by
    calc
      _ ≤ 2 * (1024 / η ^ 2) *
          (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) / (m : ℝ) ^ 2) := by
        simpa only [mul_one, mul_div_assoc] using hgap
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  have hout := (div_le_iff₀ hE).mp hh
  calc
    |gμ - gν| ≤ _ := hout
    _ = _ := by ring

private lemma window_diameter (Elo E η ε T : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : 0 < E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hd : 1 ≤ d) (hε : 0 < ε) (hT : 0 < T)
    (μ ν : Measure ℝ) (gμ gν : ℝ)
    (hμ : AtomicLaw Elo E η d μ gμ) (hν : AtomicLaw Elo E η d ν gν)
    (hnoise : ∀ t ∈ Icc 0 T, |measureCurve μ t - measureCurve ν t| ≤ 2 * ε) :
    |gμ - gν| ≤ 2 * ((1024 * E / η ^ 2) * rateWindow d ε (E * T)) := by
  by_cases heq : gμ = gν
  · simp only [heq, sub_self, abs_zero]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by positivity) (rate_window_nonneg d ε (E * T) hd hε.le))
  obtain ⟨m, hm, hmd, hgeom, _, hwin⟩ :=
    measure_joint_certificates hElo hE hη hη1 (by omega) μ ν gμ gν hμ hν heq
  let M := max 1 (((2 * m - 1 : ℕ) : ℝ) / (E * T))
  obtain ⟨c, htime, hsep, hnorm⟩ := hwin (E * T) (mul_pos hE hT)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn := certificate_noise (range (2 * m)) c
    (fun k => measureCurve μ ((k : ℝ) * (1 / (M * E))))
    (fun k => measureCurve ν ((k : ℝ) * (1 / (M * E)))) ε
    (fun k hk => hnoise _ (by
      have := htime k (mem_range.mp hk)
      simpa only [mul_div_cancel_left₀ T hE.ne'] using this)) hsep
  have hcert := hn.trans (mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 2 * ε))
  have hΔ : 0 < |gμ - gν| / E := div_pos (abs_pos.mpr (sub_ne_zero.mpr heq)) hE
  have hgap := truncated_gap η (|gμ - gν| / E) ε M m hη hη1 hΔ hε hM hm hgeom hcert
  have hr := rate_window_term_le d m ε (E * T) ⟨hm, hmd⟩
  have hh : |gμ - gν| / E ≤ 2 * (1024 / η ^ 2) * rateWindow d ε (E * T) := by
    calc
      _ ≤ 2 * (1024 / η ^ 2) *
          (min 1 (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) * M) / (m : ℝ) ^ 2) := by
        simpa only [mul_div_assoc] using hgap
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  have hout := (div_le_iff₀ hE).mp hh
  calc
    |gμ - gν| ≤ _ := hout
    _ = _ := by ring

/-- A uniform estimator on the original finite atomic measure model. -/
theorem exists_window_estimator (Elo E η T ε : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : Elo < E) (hη : 0 < η) (hη1 : η < 1)
    (hd : 1 ≤ d) (hT : 0 < T) (hε : 0 < ε) :
    ∃ G : (Icc 0 T → ℝ) → ℝ, ∀ (μ : Measure ℝ) (g : ℝ),
      AtomicLaw Elo E η d μ g → ∀ Y : Icc 0 T → ℝ,
      (∀ t : Icc 0 T, |Y t - measureCurve μ t| ≤ ε) →
      |G Y - g| ≤ (1024 * E / η ^ 2) * rateWindow d ε (E * T) := by
  refine ⟨midpointEstimator Elo E η d (Icc 0 T) ε, ?_⟩
  exact midpoint_estimator_bound Elo E η ε _ d (Icc 0 T)
    (window_diameter Elo E η ε T d hElo (hElo.trans_lt hE) hη hη1.le hd hε hT)

/-- The deterministic finite window minimax upper bound, uniformly in dimension and time. -/
theorem minimax_window_upper (Elo E η T ε : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : Elo < E) (hη : 0 < η) (hη1 : η < 1)
    (hd : 1 ≤ d) (hT : 0 < T) (hε : 0 < ε) :
    minimaxRisk Elo E η d (Icc 0 T) ε ≤
      ENNReal.ofReal ((1024 * E / η ^ 2) * rateWindow d ε (E * T)) := by
  obtain ⟨G, hG⟩ := exists_window_estimator Elo E η T ε d hElo hE hη hη1 hd hT hε
  exact minimax_of_estimator Elo E η ε _ d (Icc 0 T) G hG

/-- The all-time deterministic minimax bound with a dimension independent constant. -/
theorem minimax_all_upper (Elo E η ε : ℝ) (d : ℕ)
    (hElo : 0 ≤ Elo) (hE : Elo < E) (hη : 0 < η) (hη1 : η < 1)
    (hd : 1 ≤ d) (hε : 0 < ε) :
    minimaxRisk Elo E η d (Ici 0) ε ≤ ENNReal.ofReal ((1024 * E / η ^ 2) * rateAll d ε) := by
  apply minimax_of_estimator Elo E η ε _ d (Ici 0)
    (midpointEstimator Elo E η d (Ici 0) ε)
  exact midpoint_estimator_bound Elo E η ε _ d (Ici 0)
    (all_diameter Elo E η ε d hElo (hElo.trans_lt hE) hη hη1.le hd hε)

end D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
