/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Threshold masks give a harmonic-overlap bound on a finite observation table. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! The harmonic-overlap threshold argument for finitely many observation rows. -/

open scoped BigOperators Interval
open MeasureTheory Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

/-- Triangular discrimination for one row. The zero row contributes zero. -/
def scoreTerm (p q : ℝ) : ℝ := (p - q) ^ 2 / (p + q)

def score {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, scoreTerm (p i) (q i)

def harmonicTerm (p q : ℝ) : ℝ := p * q / (p + q)

def minimizingScore (p q : ℝ) : ℝ := q / (p + q)

theorem minimizingScore_mem_Icc {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    minimizingScore p q ∈ Icc (0 : ℝ) 1 := by
  have hsum := add_nonneg hp hq
  refine ⟨div_nonneg hq hsum, ?_⟩
  rcases hsum.eq_or_lt with h | h
  · simp [minimizingScore, ← h]
  · exact (div_le_one h).2 (le_add_of_nonneg_left hp)

theorem harmonicTerm_eq_at_minimizingScore {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    harmonicTerm p q =
      p * minimizingScore p q ^ 2 + q * (1 - minimizingScore p q) ^ 2 := by
  by_cases h : p + q = 0
  · have hp0 : p = 0 := by linarith
    have hq0 : q = 0 := by linarith
    simp [harmonicTerm, hp0, hq0]
  · unfold harmonicTerm minimizingScore
    field_simp [h]
    ring

private theorem scoreTerm_eq_sub_overlap (p q : ℝ) :
    scoreTerm p q = p + q - 4 * harmonicTerm p q := by
  by_cases h : p + q = 0
  · simp [scoreTerm, harmonicTerm, h]
  · unfold scoreTerm harmonicTerm
    field_simp [h]
    ring

variable {ι : Type*} [Fintype ι]

def harmonicOverlap (p q : ι → ℝ) : ℝ := ∑ i, harmonicTerm (p i) (q i)

theorem score_eq_sub_overlap (p q : ι → ℝ) :
    score p q = (∑ i, p i) + (∑ i, q i) - 4 * harmonicOverlap p q := by
  simp [score, harmonicOverlap, scoreTerm_eq_sub_overlap, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum]

def maskMass (p : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, p i

section Masks

variable [DecidableEq ι]

/-- Rayleigh lower bounds on the two laws at masks of the specified sizes.
In a two-basis application `rank` is the Hilbert-space dimension. -/
structure SpectralMaskGaps (p : ι → ℝ) (rank : ℕ) (A E : ℝ) : Prop where
  large : ∀ s : Finset ι, rank < s.card → A ≤ maskMass p s
  balanced : ∀ s : Finset ι, s.card = rank → E ≤ maskMass p s

private def thresholdMask (u : ι → ℝ) (t : ℝ) : Finset ι :=
  Finset.univ.filter fun i => t ≤ u i

private def rowDensity (p q u t : ℝ) : ℝ :=
  (Iic u).indicator (fun t => p * (2 * t)) t +
    (Ioi u).indicator (fun t => q * (2 * (1 - t))) t

private theorem intervalIntegrable_indicator {f : ℝ → ℝ} {a b : ℝ} {s : Set ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private theorem rowDensity_integrable (p q u a b : ℝ) :
    IntervalIntegrable (rowDensity p q u) volume a b := by
  unfold rowDensity
  apply IntervalIntegrable.add
  · exact intervalIntegrable_indicator (Continuous.intervalIntegrable (by fun_prop) _ _) measurableSet_Iic
  · exact intervalIntegrable_indicator (Continuous.intervalIntegrable (by fun_prop) _ _) measurableSet_Ioi

private theorem integral_linear (a b : ℝ) :
    (∫ t in a..b, t) = (b ^ 2 - a ^ 2) / 2 := by
  simp

private theorem integral_rowDensity (p q u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rowDensity p q u t) = p * u ^ 2 + q * (1 - u) ^ 2 := by
  have hright : (∫ t in (0 : ℝ)..1, (Ioi u).indicator (fun t => q * (2 * (1 - t))) t) =
      ∫ t in u..1, q * (2 * (1 - t)) := by
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      intervalIntegral.integral_of_le hu.2, MeasureTheory.integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi,
      sup_eq_right.mpr hu.1]
  unfold rowDensity
  rw [intervalIntegral.integral_add
    (intervalIntegrable_indicator (Continuous.intervalIntegrable (by fun_prop) _ _) measurableSet_Iic)
    (intervalIntegrable_indicator (Continuous.intervalIntegrable (by fun_prop) _ _) measurableSet_Ioi)]
  have hleft : (∫ t in (0 : ℝ)..1, (Iic u).indicator (fun t => p * (2 * t)) t) =
      ∫ t in (0 : ℝ)..u, p * (2 * t) :=
    intervalIntegral.integral_indicator (f := fun t => p * (2 * t)) hu
  rw [hleft, hright,
    intervalIntegral.integral_const_mul p (fun t : ℝ => 2 * t),
    intervalIntegral.integral_const_mul 2 (fun t : ℝ => t),
    intervalIntegral.integral_const_mul q (fun t : ℝ => 2 * (1 - t)),
    intervalIntegral.integral_const_mul 2 (fun t : ℝ => 1 - t)]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, integral_linear, integral_linear]
  simp only [smul_eq_mul]
  ring

private def thresholdDensity (p q u : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, rowDensity (p i) (q i) (u i) t

omit [DecidableEq ι] in
private theorem thresholdDensity_integrable (p q u : ι → ℝ) (a b : ℝ) :
    IntervalIntegrable (thresholdDensity p q u) volume a b := by
  have h := IntervalIntegrable.sum Finset.univ
    (fun i _ => rowDensity_integrable (p i) (q i) (u i) a b)
  convert h using 1
  funext t
  simp only [thresholdDensity, Finset.sum_apply]

private theorem thresholdDensity_eq_maskMass (p q u : ι → ℝ) (t : ℝ) :
    thresholdDensity p q u t =
      2 * t * maskMass p (thresholdMask u t) +
        2 * (1 - t) * maskMass q (thresholdMask u t)ᶜ := by
  classical
  simp only [thresholdDensity, rowDensity, Finset.sum_add_distrib, maskMass,
    Finset.mul_sum, thresholdMask]
  congr 1
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t ≤ u i <;> simp [hi, Set.indicator, mul_comm]
  · have hcomp : (Finset.univ.filter (fun i => t ≤ u i))ᶜ =
        Finset.univ.filter (fun i => u i < t) := by
      ext i
      simp
    rw [hcomp, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u i < t <;> simp [hi, Set.indicator, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem maskMass_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset ι) :
    0 ≤ maskMass p s := Finset.sum_nonneg fun i _ => hp i

private theorem density_ge_envelope (p q u : ι → ℝ) {n : ℕ} {A E t : ℝ}
    (hcard : Fintype.card ι = 2 * n)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpG : SpectralMaskGaps p n A E) (hqG : SpectralMaskGaps q n A E)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    min (2 * A * t) (min (2 * A * (1 - t)) (2 * E)) ≤ thresholdDensity p q u t := by
  rw [thresholdDensity_eq_maskMass]
  let s := thresholdMask u t
  change _ ≤ 2 * t * maskMass p s + 2 * (1 - t) * maskMass q sᶜ
  have h₀ : 0 ≤ 2 * t := by linarith [ht.1]
  have h₁ : 0 ≤ 2 * (1 - t) := by linarith [ht.2]
  have hcomp := Finset.card_compl_add_card s
  rw [hcard] at hcomp
  rcases lt_trichotomy s.card n with h | h | h
  · have hg := hqG.large sᶜ (by omega)
    have hq' := mul_le_mul_of_nonneg_left hg h₁
    have hp' := mul_nonneg h₀ (maskMass_nonneg p hp s)
    apply le_trans (min_le_right _ _) (le_trans (min_le_left _ _) _)
    linarith only [hq', hp']
  · have hp' := mul_le_mul_of_nonneg_left (hpG.balanced s h) h₀
    have hq' := mul_le_mul_of_nonneg_left (hqG.balanced sᶜ (by omega)) h₁
    apply le_trans (min_le_right _ _) (le_trans (min_le_right _ _) _)
    linarith only [hp', hq']
  · have hp' := mul_le_mul_of_nonneg_left (hpG.large s h) h₀
    have hq' := mul_nonneg h₁ (maskMass_nonneg q hq sᶜ)
    apply le_trans (min_le_left _ _) _
    linarith only [hp', hq']

private theorem integral_envelope {A E : ℝ} (hA : 0 < A) (hE : 0 ≤ E)
    (hEA : 2 * E ≤ A) :
    (∫ t in (0 : ℝ)..1, min (2 * A * t) (min (2 * A * (1 - t)) (2 * E))) =
      2 * E - 2 * E ^ 2 / A := by
  let f : ℝ → ℝ := fun t => min (2 * A * t) (min (2 * A * (1 - t)) (2 * E))
  let k := E / A
  have hk : 0 ≤ k := div_nonneg hE hA.le
  have hAk : A * k = E := mul_div_cancel₀ E hA.ne'
  have hkhalf : k ≤ 1 / 2 := by
    dsimp [k]
    apply (div_le_iff₀ hA).2
    linarith
  have hleft : (∫ t in (0 : ℝ)..k, f t) = ∫ t in (0 : ℝ)..k, 2 * A * t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hk] at ht
    apply min_eq_left
    apply le_min
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [ht.2]
    · have h := mul_le_mul_of_nonneg_left ht.2 hA.le
      nlinarith only [h, hAk]
  have hmid : (∫ t in k..(1 - k), f t) = ∫ _t in k..(1 - k), 2 * E := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (show k ≤ 1 - k by linarith)] at ht
    have hl := mul_le_mul_of_nonneg_left ht.1 hA.le
    have hr := mul_le_mul_of_nonneg_left (show k ≤ 1 - t by linarith [ht.2]) hA.le
    change min _ (min _ _) = _
    rw [min_eq_right (show 2 * E ≤ 2 * A * (1 - t) by nlinarith only [hr, hAk]),
      min_eq_right (show 2 * E ≤ 2 * A * t by nlinarith only [hl, hAk])]
  have hright : (∫ t in (1 - k)..(1 : ℝ), f t) =
      ∫ t in (1 - k)..(1 : ℝ), 2 * A * (1 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (show 1 - k ≤ 1 by linarith)] at ht
    have hr := mul_le_mul_of_nonneg_left (show 1 - t ≤ k by linarith [ht.1]) hA.le
    change min _ (min _ _) = _
    rw [min_eq_left (show 2 * A * (1 - t) ≤ 2 * E by nlinarith only [hr, hAk])]
    exact min_eq_right (mul_le_mul_of_nonneg_left
      (show 1 - t ≤ t by linarith [ht.1]) (by positivity))
  have hf (a b : ℝ) : IntervalIntegrable f volume a b := by unfold f; exact Continuous.intervalIntegrable (by fun_prop) _ _
  change (∫ t in (0 : ℝ)..1, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf 0 (1 - k)) (hf (1 - k) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hf 0 k) (hf k (1 - k)),
    hleft, hmid, hright]
  rw [intervalIntegral.integral_const_mul (2 * A) (fun t : ℝ => t),
    intervalIntegral.integral_const_mul (2 * A) (fun t : ℝ => 1 - t)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [integral_linear, integral_linear]
  dsimp [k]
  field_simp [hA.ne']
  ring

/-- The exact harmonic deficit from threshold masks on a table of `2 * n` rows. -/
theorem overlap_lower_bound_of_mask_gaps (p q : ι → ℝ) {n : ℕ} {A E : ℝ}
    (hcard : Fintype.card ι = 2 * n)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hA : 0 < A) (hE : 0 ≤ E) (hEA : 2 * E ≤ A)
    (hpG : SpectralMaskGaps p n A E) (hqG : SpectralMaskGaps q n A E) :
    2 * E - 2 * E ^ 2 / A ≤ harmonicOverlap p q := by
  let u i := minimizingScore (p i) (q i)
  have hD : (∫ t in (0 : ℝ)..1, thresholdDensity p q u t) = harmonicOverlap p q := by
    unfold thresholdDensity harmonicOverlap
    rw [intervalIntegral.integral_finsetSum (fun i _ =>
      rowDensity_integrable (p i) (q i) (u i) 0 1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_rowDensity _ _ _ (minimizingScore_mem_Icc (hp i) (hq i)),
      harmonicTerm_eq_at_minimizingScore (hp i) (hq i)]
  rw [← integral_envelope hA hE hEA, ← hD]
  exact intervalIntegral.integral_mono_on (by norm_num) (Continuous.intervalIntegrable (by fun_prop) _ _)
    (thresholdDensity_integrable p q u 0 1)
    (fun _ ht => density_ge_envelope p q u hcard hp hq hpG hqG ht)

/-- The corresponding triangular-discrimination bound for two normalized bases. -/
theorem score_upper_bound_of_mask_gaps (p q : ι → ℝ) {n : ℕ} {A E : ℝ}
    (hcard : Fintype.card ι = 2 * n)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 2) (hqsum : ∑ i, q i = 2)
    (hA : 0 < A) (hE : 0 ≤ E) (hEA : 2 * E ≤ A)
    (hpG : SpectralMaskGaps p n A E) (hqG : SpectralMaskGaps q n A E) :
    score p q ≤ 4 - 8 * E + 8 * E ^ 2 / A := by
  rw [score_eq_sub_overlap, hpsum, hqsum]
  have h := overlap_lower_bound_of_mask_gaps p q hcard hp hq hA hE hEA hpG hqG
  simp only [mul_div_assoc] at h ⊢
  linarith only [h]

end Masks

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
