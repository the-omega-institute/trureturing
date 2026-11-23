/- GID: D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/ContinuousSpectralPerturbations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interval averaging bounds the near-collisions of a perturbed spectrum. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ProductMeasure
import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/-! Closed near-collision bands on continuous perturbation intervals. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialFrequency)
open scoped ENNReal NNReal

namespace D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations

private def intervalNoise (radius : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * radius))⁻¹ • volume.restrict (Icc (-radius) radius)

private theorem intervalNoise_probability {radius : ℝ} (hradius : 0 < radius) :
    IsProbabilityMeasure (intervalNoise radius) := by
  constructor
  have hlen : radius - -radius = 2 * radius := by ring
  rw [intervalNoise, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, hlen]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

private theorem intervalNoise_affine_local {radius a b η : ℝ}
    (hradius : 0 < radius) (ha : a ≠ 0) :
    intervalNoise radius {x | |a * x + b| ≤ η} ≤ ENNReal.ofReal (η / (|a| * radius)) := by
  let center := -b / a
  let reach := η / |a|
  have hfactor (x : ℝ) : a * x + b = a * (x - center) := by
    dsimp [center]
    field_simp
    ring
  have hset : {x : ℝ | |a * x + b| ≤ η} = Icc (center - reach) (center + reach) := by
    ext x
    change |a * x + b| ≤ η ↔ _
    rw [hfactor, abs_mul, mul_comm |a|, ← le_div_iff₀ (abs_pos.mpr ha), abs_le]
    change -reach ≤ x - center ∧ x - center ≤ reach ↔ _
    rw [Set.mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add, neg_add_eq_sub, add_comm reach]
  have hlen : center + reach - (center - reach) = 2 * reach := by ring
  have hmeasure : volume (Icc (center - reach) (center + reach) ∩
      Icc (-radius) radius) ≤ ENNReal.ofReal (2 * reach) := by
    calc
      _ ≤ volume (Icc (center - reach) (center + reach)) := measure_mono inter_subset_left
      _ = _ := by rw [Real.volume_Icc, hlen]
  rw [hset, intervalNoise, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Icc, smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal (2 * radius))⁻¹ * ENNReal.ofReal (2 * reach) :=
      by gcongr
    _ = ENNReal.ofReal (reach / radius) := by
      rw [mul_comm, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      field_simp
    _ = _ := by simp [reach, div_div]

private theorem intervalNoise_fin_affine {n : ℕ} (radius a : Fin (n + 1) → ℝ)
    (b η : ℝ) (hradius : ∀ j, 0 < radius j) (i : Fin (n + 1)) (ha : a i ≠ 0) :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |(∑ j, a j * x j) + b| ≤ η} ≤ ENNReal.ofReal (η / (|a i| * radius i)) := by
  let μ (j : Fin (n + 1)) := intervalNoise (radius j)
  have (j : Fin (n + 1)) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  let ν := Measure.pi fun j : Fin n => μ (i.succAbove j)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let rest (y : Fin n → ℝ) := (∑ j : Fin n, a (i.succAbove j) * y j) + b
  let S := {xy : ℝ × (Fin n → ℝ) | |a i * xy.1 + rest xy.2| ≤ η}
  have hS : MeasurableSet S := by
    change MeasurableSet {xy : ℝ × (Fin n → ℝ) | |a i * xy.1 + rest xy.2| ≤ η}
    apply measurableSet_le _ measurable_const
    unfold rest
    fun_prop
  have hpre : e ⁻¹' S = {x | |(∑ j, a j * x j) + b| ≤ η} := by
    ext x
    change |a i * x i + rest (fun j => x (i.succAbove j))| ≤ η ↔
      |(∑ j, a j * x j) + b| ≤ η
    simp only [rest, i.sum_univ_succAbove (f := fun j => a j * x j), add_assoc]
  have hp : MeasurePreserving e (Measure.pi μ) ((μ i).prod ν) :=
    measurePreserving_piFinSuccAbove μ i
  rw [← hpre, ← Measure.map_apply hp.measurable hS, hp.map_eq, Measure.prod_apply_symm hS]
  calc
    _ ≤ ∫⁻ _, ENNReal.ofReal (η / (|a i| * radius i)) ∂ν := by
      apply lintegral_mono
      intro y
      change intervalNoise (radius i) {x | |a i * x + rest y| ≤ η} ≤ _
      exact intervalNoise_affine_local (b := rest y) (η := η) (hradius i) ha
    _ = _ := by simp [ν]

private theorem intervalNoise_pi_affine {J : Type*} [Fintype J] (radius a : J → ℝ)
    (b η : ℝ) (hradius : ∀ j, 0 < radius j) (i : J) (ha : a i ≠ 0) :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |(∑ j, a j * x j) + b| ≤ η} ≤ ENNReal.ofReal (η / (|a i| * radius i)) := by
  let μ (j : J) := intervalNoise (radius j)
  have (j : J) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  let S := {x : J → ℝ | |(∑ j, a j * x j) + b| ≤ η}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    fun_prop
  have hcard : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  let e : Fin (n + 1) ≃ J := (Fintype.equivFinOfCardEq hn).symm
  let move := MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e
  have hmove : MeasurePreserving move (Measure.pi fun j => μ (e j)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hpre : move ⁻¹' S = {x | |(∑ j, a (e j) * x j) + b| ≤ η} := by
    ext x
    change |(∑ j, a j * move x j) + b| ≤ η ↔ _
    have heq : (∑ j, a (e j) * x j) = ∑ j, a j * move x j :=
      Fintype.sum_equiv e _ _ (fun j => by simp [move, MeasurableEquiv.piCongrLeft_apply_apply])
    rw [mem_ofPred_eq, heq]
  change Measure.pi μ S ≤ _
  rw [← hmove.map_eq, Measure.map_apply hmove.measurable hS, hpre]
  have h := intervalNoise_fin_affine (radius ∘ e) (a ∘ e) b η (fun j => hradius (e j)) (e.symm i)
  simpa [μ, Function.comp_def] using h (by simpa using ha)

/-- Maximum perturbation radius after weighting each coordinate by the coefficient difference. -/
def pairRadius {J : Type*} [Fintype J] (radius : J → ℝ) (m n : J → ℕ) : ℝ :=
  (univ.sup fun j => (|(m j : ℝ) - (n j : ℝ)| * radius j).toNNReal : ℝ≥0)

private theorem pairRadius_attained {J : Type*} [Fintype J] (radius : J → ℝ)
    (hradius : ∀ j, 0 < radius j) {m n : J → ℕ} (hmn : m ≠ n) :
    ∃ i, (m i : ℝ) - (n i : ℝ) ≠ 0 ∧
      pairRadius radius m n = |(m i : ℝ) - (n i : ℝ)| * radius i := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ n j := by
    by_contra! h
    exact hmn (funext h)
  let q (i : J) := (|(m i : ℝ) - (n i : ℝ)| * radius i).toNNReal
  have hnonneg (i : J) : 0 ≤ |(m i : ℝ) - (n i : ℝ)| * radius i :=
    mul_nonneg (abs_nonneg _) (hradius i).le
  have hpos : 0 < q j := by
    have hreal : (m j : ℝ) ≠ (n j : ℝ) := by exact_mod_cast hj
    exact Real.toNNReal_pos.mpr (mul_pos (abs_pos.mpr (sub_ne_zero.mpr hreal)) (hradius j))
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (univ : Finset J)
    ⟨j, mem_univ j⟩ q
  have hposi : 0 < q i := hpos.trans_le (hi ▸ (le_sup (f := q) (mem_univ j)))
  have hnonzero : (m i : ℝ) - (n i : ℝ) ≠ 0 := by
    intro heq
    simp [q, heq] at hposi
  refine ⟨i, hnonzero, ?_⟩
  change ((univ.sup q : ℝ≥0) : ℝ) = _
  rw [hi]
  exact Real.coe_toNNReal _ (hnonneg i)

private theorem pair_event_measure_le {J : Type*} [Fintype J] (g radius : J → ℝ)
    (hradius : ∀ j, 0 < radius j) {m n : J → ℕ} (hmn : m ≠ n) {η : ℝ} :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |monomialFrequency (fun j => g j + x j) m -
        monomialFrequency (fun j => g j + x j) n| ≤ η} ≤
      min 1 (ENNReal.ofReal (η / pairRadius radius m n)) := by
  let μ (j : J) := intervalNoise (radius j)
  have (j : J) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  obtain ⟨i, hi, hmax⟩ := pairRadius_attained radius hradius hmn
  let a (j : J) := (m j : ℝ) - (n j : ℝ)
  let b := ∑ j, a j * g j
  have hdiff (x : J → ℝ) :
      monomialFrequency (fun j => g j + x j) m -
        monomialFrequency (fun j => g j + x j) n = (∑ j, a j * x j) + b := by
    unfold monomialFrequency
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun j _ => by dsimp [a]; ring)
  simp_rw [hdiff]
  change Measure.pi μ _ ≤ _
  refine le_min (prob_le_one) ?_
  rw [hmax]
  exact intervalNoise_pi_affine radius a b η hradius i hi

private theorem exists_within_expected_budget {Ω K : Type*} [MeasurableSpace Ω] [Countable K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (loss : K → Ω → ℝ≥0∞)
    (hloss : ∀ k, Measurable (loss k)) (good : Ω → Prop) (hgood : ∀ᵐ x ∂μ, good x)
    (hbudget : (∑' k, ∫⁻ x, loss k x ∂μ) ≤ 1) :
    ∃ x, good x ∧ ∀ k, loss k x ≤ 1 := by
  let total (x : Ω) := ∑' k, loss k x
  have htotal : Measurable total := Measurable.tsum hloss
  have hmean : (∫⁻ x, total x ∂μ) ≤ 1 := by
    exact (lintegral_tsum (fun k => (hloss k).aemeasurable)).trans_le hbudget
  by_contra! hbad
  have hlt : ∀ᵐ x ∂μ, 1 < total x := hgood.mono fun x hx => by
    obtain ⟨k, hk⟩ := hbad x hx
    exact hk.trans_le (ENNReal.le_tsum (f := fun j => loss j x) k)
  have h := lintegral_strict_mono (f := fun _ : Ω => 1) (NeZero.ne μ)
    htotal.aemeasurable (by simp) hlt
  exact (not_lt_of_ge hmean) (by simpa using h)

end D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
