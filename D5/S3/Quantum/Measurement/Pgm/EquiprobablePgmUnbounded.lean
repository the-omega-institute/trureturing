/- GID: D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmUnbounded
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Pgm/EquiprobablePgmUnbounded
   mirror-E: none(waiver:universal-parameter-proof)
   anchors: []
   utility: none
   digest: Unbounded centered PGM ratio at fixed dimension and label count. -/

import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Haobo Ma and Wenlin Zhang, in that order, 4 November 2026, CC BY 4.0
for this new note only. The symmetric score calculation is credited to
Hyunho Cha. The anonymous mechanism and old rational note retain their
separate attribution and license status. The new content is uniform
actual-state unboundedness, not another proof of the old negation.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmUnbounded
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison (symmetric_scores)
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore success)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

/-- The fixed (d,N)=(2,3) mixed-state family of the new note. -/
def states (ε : ℝ) := rho (1 - ε ^ 6) (ε ^ 3 / 2) (1 - ε ^ 4)

def H (ε : ℝ) : ℝ := (1 + 2 * ε ^ 2) * (3 - ε ^ 4 * (1 + 2 * ε ^ 2))

private theorem domain (ε : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 8) :
    0 < 1 - ε ^ 6 ∧ 1 - ε ^ 6 < 1 ∧
    0 < 1 - ε ^ 4 ∧ 1 - ε ^ 4 < 1 ∧
    0 < (1 - ε ^ 6) * (1 - (1 - ε ^ 6)) - (ε ^ 3 / 2) ^ 2 ∧
    |(1 - ε ^ 4) - (1 - ε ^ 6)| ≤ ε ^ 3 / 2 ∧ 3 < H ε := by
  have hε1 : ε < 1 := by linarith
  have he2 := pow_le_pow_left₀ hε.le hεhi 2
  have he4 := pow_le_pow_left₀ hε.le hεhi 4
  have he6 := pow_le_pow_left₀ hε.le hεhi 6
  norm_num at he2 he4 he6
  have hp4 : 0 < ε ^ 4 := pow_pos hε _
  have hp6 : 0 < ε ^ 6 := pow_pos hε _
  have hp3 : 0 < ε ^ 3 := pow_pos hε _
  have hdet : 0 < ε ^ 6 * (3 / 4 - ε ^ 6) := mul_pos hp6 (by linarith)
  have hm := mul_le_mul_of_nonneg_left
    (show ε * (1 - ε ^ 2) ≤ 1 / 2 by nlinarith [mul_nonneg hε.le (sq_nonneg ε)]) hp3.le
  have hload : |(1 - ε ^ 4) - (1 - ε ^ 6)| ≤ ε ^ 3 / 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hp4.le (show 0 ≤ 1 - ε ^ 2 by linarith)]
    · nlinarith
  have hH : 3 < H ε := by
    have hsmall : 0 < 6 - ε ^ 2 * (1 + 2 * ε ^ 2) ^ 2 := by
      have hsq : (1 + 2 * ε ^ 2) ^ 2 ≤ 2 := by nlinarith [sq_nonneg (ε ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)]
    have hmH := mul_pos (sq_pos_of_pos hε) hsmall
    dsimp [H]
    nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, hload, hH⟩
  nlinarith

/-- On the entire interval the states are strictly positive (hence mixed), the
unique optimum has exactly two active labels, and both actual CFC scores have
these exact formulas. -/
theorem family (ε : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 8) :
    (∀ i, (states ε i).PosDef ∧ trace (states ε i) = 1) ∧
    finitePOVM pairPovm ∧
    (∀ E, finitePOVM E →
      ((∀ F, finitePOVM F → success (states ε) F ≤ success (states ε) E) ↔
        E = pairPovm)) ∧
    success (states ε) pairPovm = (1 + ε ^ 3) / 3 ∧
    Finset.univ.filter (fun i => pairPovm i ≠ 0) = {0, 1} ∧
    pgmScore (states ε) {0, 1} - 1 / 3 = ε ^ 3 / (6 * Real.sqrt (1 - ε ^ 6)) ∧
    pgmScore (states ε) Finset.univ - 1 / 3 =
      ε ^ 4 * (1 / (3 * Real.sqrt (H ε)) + 2 * (1 - ε ^ 2) ^ 2 / (3 * H ε)) ∧
    3 < H ε := by
  obtain ⟨ha, ha1, hc, hc1, hd, hload, hH⟩ := domain ε hε hεhi
  have hp := pair_classification (1 - ε ^ 6) (ε ^ 3 / 2) (1 - ε ^ 4)
    (by positivity) hload
  have hs := symmetric_scores (1 - ε ^ 6) (ε ^ 3 / 2) (1 - ε ^ 4) ha ha1 hc hc1
  have hq : (1 - ε ^ 6) * (1 - (1 - ε ^ 6)) = (ε ^ 3) ^ 2 * (1 - ε ^ 6) := by ring
  have hD : (2 * (1 - ε ^ 6) + (1 - ε ^ 4)) *
      (3 - 2 * (1 - ε ^ 6) - (1 - ε ^ 4)) = (ε ^ 2) ^ 2 * H ε := by
    dsimp [H]; ring
  have hqroot : Real.sqrt ((1 - ε ^ 6) * (1 - (1 - ε ^ 6))) =
      ε ^ 3 * Real.sqrt (1 - ε ^ 6) := by
    rw [hq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hDroot : Real.sqrt ((2 * (1 - ε ^ 6) + (1 - ε ^ 4)) *
      (3 - 2 * (1 - ε ^ 6) - (1 - ε ^ 4))) = ε ^ 2 * Real.sqrt (H ε) := by
    rw [hD, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
  refine ⟨states_posDef _ _ _ ha hc hc1 hd, hp.1, hp.2.2, ?_, ?_, ?_, ?_, hH⟩
  · change success (rho _ _ _) pairPovm = _
    rw [hp.2.1]
    ring
  · have h := (complete_classification (1 - ε ^ 6) (ε ^ 3 / 2) (1 - ε ^ 4)
        (by positivity)).2.2
    simp only [if_pos hload] at h
    simpa only [optimalPovm, if_pos hload] using h
  · change pgmScore (rho _ _ _) {0, 1} - 1 / 3 = _
    rw [hs.1, hqroot]
    field_simp
    ring
  · change pgmScore (rho _ _ _) Finset.univ - 1 / 3 = _
    rw [hs.2, hDroot, hD]
    field_simp
    ring

/-- A uniform lower bound for the actual centered ratio. The strict coarser
3/(8 epsilon) bound gives a convenient every-real-constant choice. -/
theorem uniform_ratio (ε : ℝ) (hε : 0 < ε) (hεhi : ε ≤ 1 / 8) :
    0 < pgmScore (states ε) Finset.univ - 1 / 3 ∧
    3 / (2 * (2 + Real.sqrt 3) * ε) ≤
      (pgmScore (states ε) {0, 1} - 1 / 3) /
        (pgmScore (states ε) Finset.univ - 1 / 3) ∧
    3 / (8 * ε) < (pgmScore (states ε) {0, 1} - 1 / 3) /
        (pgmScore (states ε) Finset.univ - 1 / 3) := by
  have hf := family ε hε hεhi
  have ha := (domain ε hε hεhi).1
  have hH : 3 < H ε := hf.2.2.2.2.2.2.2
  have hH0 : 0 < H ε := by linarith
  have hT : 0 < Real.sqrt (H ε) := Real.sqrt_pos.mpr hH0
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3hi : Real.sqrt 3 < 2 := by nlinarith
  have hThi : Real.sqrt 3 ≤ Real.sqrt (H ε) := Real.sqrt_le_sqrt hH.le
  have hS : 0 < Real.sqrt (1 - ε ^ 6) := Real.sqrt_pos.mpr ha
  have hShi : Real.sqrt (1 - ε ^ 6) ≤ 1 := by
    nlinarith [Real.sq_sqrt ha.le, pow_nonneg hε.le 6]
  have he2 : ε ^ 2 ≤ 1 := by
    nlinarith [pow_le_pow_left₀ hε.le hεhi 2]
  have hpop : (1 - ε ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
  let L := 1 / (3 * Real.sqrt (H ε)) + 2 * (1 - ε ^ 2) ^ 2 / (3 * H ε)
  have hL : 0 < L := by dsimp [L]; positivity
  have hLhi : L ≤ (2 + Real.sqrt 3) / 9 := by
    have h1 : 1 / (3 * Real.sqrt (H ε)) ≤ Real.sqrt 3 / 9 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 9)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hThi hs3.le]
    have h2 : 2 * (1 - ε ^ 2) ^ 2 / (3 * H ε) ≤ 2 / 9 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 9)).mpr
      nlinarith
    dsimp [L]
    linarith
  rw [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1]
  change 0 < ε ^ 4 * L ∧ _
  have hfull : 0 < ε ^ 4 * L := by positivity
  have hmain : 3 / (2 * (2 + Real.sqrt 3) * ε) ≤
      (ε ^ 3 / (6 * Real.sqrt (1 - ε ^ 6))) / (ε ^ 4 * L) := by
    apply (le_div_iff₀ hfull).mpr
    apply (le_div_iff₀ (by positivity : 0 < 6 * Real.sqrt (1 - ε ^ 6))).mpr
    have hmul := mul_le_mul_of_nonneg_left hLhi (by positivity : 0 ≤ Real.sqrt (1 - ε ^ 6))
    have hcoef : 6 * Real.sqrt (1 - ε ^ 6) * L ≤ 2 * (2 + Real.sqrt 3) / 3 := by
      nlinarith [mul_le_mul_of_nonneg_right hShi (by positivity : 0 ≤ (2 + Real.sqrt 3) / 9)]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (2 + Real.sqrt 3) * ε)).mpr
    have hm := mul_le_mul_of_nonneg_left hcoef (by positivity : 0 ≤ 3 * ε ^ 4)
    nlinarith
  refine ⟨hfull, hmain, lt_of_lt_of_le ?_ hmain⟩
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_pos hε (show 0 < 2 - Real.sqrt 3 by linarith)]

/-- Every positive real target is exceeded with actual strictly positive mixed
states at fixed (d,N,m)=(2,3,2) and the unique optimum (Q+,Q-,0). -/
theorem every_constant (C : ℝ) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 8 ∧
      (∀ i, (states ε i).PosDef ∧ trace (states ε i) = 1) ∧
      finitePOVM pairPovm ∧
      (∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (states ε) F ≤ success (states ε) E) ↔
          E = pairPovm)) ∧
      Finset.univ.filter (fun i => pairPovm i ≠ 0) = {0, 1} ∧
      C * (pgmScore (states ε) Finset.univ - 1 / 3) <
        pgmScore (states ε) {0, 1} - 1 / 3 ∧
      0 < pgmScore (states ε) Finset.univ - 1 / 3 := by
  let ε := min (1 / 8 : ℝ) (3 / (8 * C)) / 2
  have hm : 0 < min (1 / 8 : ℝ) (3 / (8 * C)) := lt_min (by norm_num) (by positivity)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεm : ε < min (1 / 8 : ℝ) (3 / (8 * C)) := by dsimp [ε]; linarith
  have hεhi : ε ≤ 1 / 8 := le_trans hεm.le (min_le_left _ _)
  have hεC : ε < 3 / (8 * C) := lt_of_lt_of_le hεm (min_le_right _ _)
  obtain ⟨hρ, hE, hopt, hscore, hactive, hA, hfull, hH⟩ := family ε hε hεhi
  obtain ⟨hp, hr, hr'⟩ := uniform_ratio ε hε hεhi
  have hc : C < 3 / (8 * ε) := by
    apply (lt_div_iff₀ (by positivity : 0 < 8 * ε)).mpr
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * C)).mp hεC
    nlinarith
  refine ⟨ε, hε, hεhi, hρ, hE, hopt, hactive, ?_, hp⟩
  exact (lt_div_iff₀ hp).mp (lt_trans hc hr')

open Filter Topology in
private theorem small_parameters : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 / 8 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)).filter_mono nhdsWithin_le_nhds]
    with ε hε hhi
  exact ⟨hε, hhi.le⟩

open Filter Topology in
/-- Both advantages vanish and the raw score ratio tends to one. The centered
ratio diverges. These limits make no positive spectral-floor or all-pure claim. -/
theorem score_limits :
    Tendsto (fun ε : ℝ => pgmScore (states ε) {0, 1} - 1 / 3) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => pgmScore (states ε) Finset.univ - 1 / 3) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => pgmScore (states ε) {0, 1} /
      pgmScore (states ε) Finset.univ) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun ε : ℝ => (pgmScore (states ε) {0, 1} - 1 / 3) /
      (pgmScore (states ε) Finset.univ - 1 / 3)) (𝓝[>] 0) atTop := by
  have hcA : ContinuousAt (fun ε : ℝ => ε ^ 3 / (6 * Real.sqrt (1 - ε ^ 6))) 0 := by
    fun_prop (disch := norm_num)
  have hcP : ContinuousAt (fun ε : ℝ => ε ^ 4 *
      (1 / (3 * Real.sqrt (H ε)) + 2 * (1 - ε ^ 2) ^ 2 / (3 * H ε))) 0 := by
    unfold H
    fun_prop (disch := norm_num)
  have hlimA : Tendsto (fun ε : ℝ => pgmScore (states ε) {0, 1} - 1 / 3)
      (𝓝[>] 0) (𝓝 0) := by
    have heq : (fun ε : ℝ => ε ^ 3 / (6 * Real.sqrt (1 - ε ^ 6))) =ᶠ[𝓝[>] 0]
        (fun ε : ℝ => pgmScore (states ε) {0, 1} - 1 / 3) := by
      filter_upwards [small_parameters] with ε hε
      exact (family ε hε.1 hε.2).2.2.2.2.2.1.symm
    apply Tendsto.congr' heq
    simpa using hcA.tendsto.mono_left nhdsWithin_le_nhds
  have hlimP : Tendsto (fun ε : ℝ => pgmScore (states ε) Finset.univ - 1 / 3)
      (𝓝[>] 0) (𝓝 0) := by
    have heq : (fun ε : ℝ => ε ^ 4 *
        (1 / (3 * Real.sqrt (H ε)) + 2 * (1 - ε ^ 2) ^ 2 / (3 * H ε))) =ᶠ[𝓝[>] 0]
        (fun ε : ℝ => pgmScore (states ε) Finset.univ - 1 / 3) := by
      filter_upwards [small_parameters] with ε hε
      exact (family ε hε.1 hε.2).2.2.2.2.2.2.1.symm
    apply Tendsto.congr' heq
    simpa [H] using hcP.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨hlimA, hlimP, ?_, ?_⟩
  · have ha := hlimA.add_const (1 / 3 : ℝ)
    have hp := hlimP.add_const (1 / 3 : ℝ)
    simp only [sub_add_cancel, zero_add] at ha hp
    convert ha.div hp (by norm_num : (1 / 3 : ℝ) ≠ 0) using 1 <;> norm_num
  · apply tendsto_atTop.2
    intro C
    let C' := max C 1
    have hC' : 0 < C' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hevent : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 3 / (8 * C') :=
      (eventually_lt_nhds (by positivity : (0 : ℝ) < 3 / (8 * C'))).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [small_parameters, hevent] with ε hε hsmall
    have hε0 : 0 < ε := hε.1
    have hcr : C' < 3 / (8 * ε) := by
      apply (lt_div_iff₀ (by positivity : 0 < 8 * ε)).mpr
      have hm := (lt_div_iff₀ (by positivity : 0 < 8 * C')).mp hsmall
      nlinarith
    exact le_trans (le_max_left C 1) (le_trans hcr.le (uniform_ratio ε hε.1 hε.2).2.2.le)

/-- Actual support averages have these least spectral values. They vanish in
the limit, so this construction supplies no positive uniform spectral floor. -/
theorem spectral_minima (ε : ℝ) (hε : 0 < ε) (hhi : ε ≤ 1 / 8) :
    IsLeast (spectrum ℝ (∑ i ∈ ({0, 1} : Finset (Fin 3)),
      (1 / (3 : ℂ)) • states ε i)) (2 * ε ^ 6 / 3) ∧
    IsLeast (spectrum ℝ (∑ i : Fin 3, (1 / (3 : ℂ)) • states ε i))
      ((ε ^ 4 + 2 * ε ^ 6) / 3) := by
  have hA : (∑ i ∈ ({0, 1} : Finset (Fin 3)), (1 / (3 : ℂ)) • states ε i) =
      diagonal ![(((2 * (1 - ε ^ 6) / 3 : ℝ)) : ℂ), ((2 * ε ^ 6 / 3 : ℝ) : ℂ)] := by
    rw [Finset.sum_pair (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [states, rho] <;> push_cast <;> ring
  have hP : (∑ i : Fin 3, (1 / (3 : ℂ)) • states ε i) =
      diagonal ![(((3 - ε ^ 4 - 2 * ε ^ 6) / 3 : ℝ) : ℂ),
        (((ε ^ 4 + 2 * ε ^ 6) / 3 : ℝ) : ℂ)] := by
    rw [Fin.sum_univ_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [states, rho] <;> push_cast <;> ring
  have h6 := pow_le_pow_left₀ hε.le hhi 6
  have h4 := pow_le_pow_left₀ hε.le hhi 4
  norm_num at h6 h4
  have hspectrum (u v r : ℝ) : r ∈ spectrum ℝ (diagonal ![(u : ℂ), (v : ℂ)]) ↔
      r = u ∨ r = v := by
    rw [← spectrum.algebraMap_mem_iff ℂ, spectrum_diagonal]
    change (∃ i : Fin 2, ![(u : ℂ), (v : ℂ)] i = (r : ℂ)) ↔ _
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · left; change (u : ℂ) = (r : ℂ) at hi; exact_mod_cast hi.symm
      · right; change (v : ℂ) = (r : ℂ) at hi; exact_mod_cast hi.symm
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  constructor
  · rw [hA]
    constructor
    · exact (hspectrum _ _ _).mpr (Or.inr rfl)
    · intro r hr
      rcases (hspectrum _ _ _).mp hr with rfl | rfl <;> linarith
  · rw [hP]
    constructor
    · exact (hspectrum _ _ _).mpr (Or.inr rfl)
    · intro r hr
      rcases (hspectrum _ _ _).mp hr with rfl | rfl <;> linarith

open Filter Topology in
/-- The infima of the actual two average spectra tend to zero. The IsLeast
identities above identify them throughout the entire physical interval. -/
theorem spectral_floor_limits :
    Tendsto (fun ε : ℝ => sInf (spectrum ℝ
      (∑ i ∈ ({0, 1} : Finset (Fin 3)), (1 / (3 : ℂ)) • states ε i)))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => sInf (spectrum ℝ
      (∑ i : Fin 3, (1 / (3 : ℂ)) • states ε i))) (𝓝[>] 0) (𝓝 0) := by
  have hA : (fun ε : ℝ => sInf (spectrum ℝ
      (∑ i ∈ ({0, 1} : Finset (Fin 3)), (1 / (3 : ℂ)) • states ε i)))
      =ᶠ[𝓝[>] 0] (fun ε => 2 * ε ^ 6 / 3) := by
    filter_upwards [small_parameters] with ε hε
    exact (spectral_minima ε hε.1 hε.2).1.csInf_eq
  have hP : (fun ε : ℝ => sInf (spectrum ℝ
      (∑ i : Fin 3, (1 / (3 : ℂ)) • states ε i)))
      =ᶠ[𝓝[>] 0] (fun ε => (ε ^ 4 + 2 * ε ^ 6) / 3) := by
    filter_upwards [small_parameters] with ε hε
    exact (spectral_minima ε hε.1 hε.2).2.csInf_eq
  constructor
  · have hc : ContinuousAt (fun ε : ℝ => 2 * ε ^ 6 / 3) 0 := by fun_prop
    apply (show Tendsto (fun ε : ℝ => 2 * ε ^ 6 / 3) (𝓝[>] 0) (𝓝 0) from by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact hA.symm
  · have hc : ContinuousAt (fun ε : ℝ => (ε ^ 4 + 2 * ε ^ 6) / 3) 0 := by fun_prop
    apply (show Tendsto (fun ε : ℝ => (ε ^ 4 + 2 * ε ^ 6) / 3) (𝓝[>] 0) (𝓝 0) from by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact hP.symm

end D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmUnbounded

/- Escape-audit delivery: four source-bound registrations are currently validated
for SupportIdentity.centered_identity/random_guessing_le and
Symmetric.states_posDef/pair_classification. The remaining theorem-specific
bindings are unfinished and disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
That issue is not proof, registration validation or independent approval. -/
