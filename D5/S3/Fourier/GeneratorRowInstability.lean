/- GID: D5/S3/Fourier/GeneratorRowInstability
   generality: I
   mirror-B: D5/B/S3/Fourier/GeneratorRowInstability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/GeneratorRowInstability.claim; result=D5/S3/Fourier/GeneratorRowInstability.result; claim=D5/S3/Fourier/GeneratorRowInstability.claim
   digest: Positive real order-nine signals obstruct source-uniform generator-row stability. -/

import D5.S3.Fourier.FullBispectrumStability
import D5.S3.AnalyticClosure.ComplexPowerDifference

namespace D5.S3.Fourier.GeneratorRowInstability

open Finset
open scoped BigOperators ComplexConjugate
open FullBispectrumStability (cyclic_parseval dft_translation unit_mul_conj)

noncomputable section

/-- The source spectrum, in the unnormalized negative-exponent convention. -/
def sourceSpectrum (A : ℝ) (k : ZMod 9) : ℂ :=
  if k = 0 then (2 * A + 7 : ℝ) else if k = 3 ∨ k = 6 then (A : ℂ) else 1

/-- Constant phase blocks put all generator defects between unit amplitudes. -/
def blockPhase (u : ℂ) (k : ZMod 9) : ℂ :=
  if k = 2 ∨ k = 3 ∨ k = 4 then u else
    if k = 5 ∨ k = 6 ∨ k = 7 then conj u else 1

def targetSpectrum (A : ℝ) (u : ℂ) (k : ZMod 9) : ℂ :=
  sourceSpectrum A k * blockPhase u k

def sourceSignal (A : ℝ) : ZMod 9 → ℂ := ZMod.dft.symm (sourceSpectrum A)

def targetSignal (A : ℝ) (u : ℂ) : ZMod 9 → ℂ :=
  ZMod.dft.symm (targetSpectrum A u)

def bispectrum (F : ZMod 9 → ℂ) (k l : ZMod 9) : ℂ :=
  F k * F l * conj (F (k + l))

def countingError (f g : ZMod 9 → ℂ) (t : ZMod 9) : ℝ :=
  ∑ x, ‖g x - f (x - t)‖ ^ 2

private lemma univ_nine : (univ : Finset (ZMod 9)) = {0,1,2,3,4,5,6,7,8} := by
  decide

private lemma nine_cases (k : ZMod 9) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by
  have h : ∀ k : ZMod 9,
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by
    decide
  exact h k

private lemma source_norm (A : ℝ) (hA : 1 ≤ A) (k : ZMod 9) :
    ‖sourceSpectrum A k‖ = if k = 0 then 2 * A + 7 else
      if k = 3 ∨ k = 6 then A else 1 := by
  have ha : 0 ≤ A := by linarith
  have hd : 0 ≤ 2 * A + 7 := by linarith
  unfold sourceSpectrum
  split_ifs <;> simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hd, norm_one]

private lemma spectrum_norm (A : ℝ) (hA : 1 ≤ A) (u : ℂ) (hu : ‖u‖ = 1)
    (k : ZMod 9) : ‖targetSpectrum A u k‖ = ‖sourceSpectrum A k‖ ∧
      1 ≤ ‖sourceSpectrum A k‖ ∧ ‖sourceSpectrum A k‖ ≤ ‖sourceSpectrum A 0‖ := by
  have hphase : ‖blockPhase u k‖ = 1 := by
    unfold blockPhase
    split_ifs <;> simp only [hu, Complex.norm_conj, norm_one]
  constructor
  · rw [targetSpectrum, norm_mul, hphase, mul_one]
  · simp only [source_norm A hA k, source_norm A hA 0, if_pos rfl]
    split_ifs <;> constructor <;> linarith

private lemma hermitian (A : ℝ) (u : ℂ) (k : ZMod 9) :
    sourceSpectrum A (-k) = conj (sourceSpectrum A k) ∧
      targetSpectrum A u (-k) = conj (targetSpectrum A u k) := by
  rcases nine_cases k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num (config := { decide := true, congrConsts := false })
    [sourceSpectrum, targetSpectrum, blockPhase, map_mul, Complex.conj_ofNat]

private lemma inverse_real (F : ZMod 9 → ℂ)
    (hF : ∀ k, F (-k) = conj (F k)) (x : ZMod 9) :
    (ZMod.dft.symm F x).im = 0 := by
  have h : conj (ZMod.dft.symm F x) = ZMod.dft.symm F x := by
    rw [ZMod.invDFT_apply]
    simp only [smul_eq_mul, map_mul, map_sum, map_inv₀, map_natCast]
    congr 1
    apply Fintype.sum_equiv (Equiv.neg (ZMod 9))
    intro k
    simp only [Equiv.neg_apply, neg_mul, hF, ← AddChar.map_neg_eq_conj]
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

private lemma inverse_lower (A : ℝ) (hA : 1 ≤ A) (F : ZMod 9 → ℂ)
    (hzero : F 0 = (2 * A + 7 : ℝ))
    (hnorm : ∀ k, ‖F k‖ = ‖sourceSpectrum A k‖) (x : ZMod 9) :
    (1 : ℝ) / 9 ≤ (ZMod.dft.symm F x).re := by
  have hn : ∑ k ∈ (univ : Finset (ZMod 9)).erase 0, ‖F k‖ = 2 * A + 6 := by
    simp_rw [hnorm]
    rw [univ_nine]
    norm_num (config := { decide := true })
      [Fin.ext_iff, sourceSpectrum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ A)]
    ring
  have hb : -(2 * A + 6) ≤
      (∑ k ∈ (univ : Finset (ZMod 9)).erase 0,
        ZMod.stdAddChar (k * x) * F k).re := by
    have h := (fun z => (abs_le.mp (Complex.abs_re_le_norm z)).1)
      (∑ k ∈ (univ : Finset (ZMod 9)).erase 0, ZMod.stdAddChar (k * x) * F k)
    have hs := norm_sum_le ((univ : Finset (ZMod 9)).erase 0)
      (fun k => ZMod.stdAddChar (k * x) * F k)
    simp only [norm_mul, AddChar.norm_apply, one_mul] at hs
    rw [hn] at hs
    linarith
  rw [ZMod.invDFT_apply, smul_eq_mul,
    ← sum_erase_add _ _ (mem_univ (0 : ZMod 9))]
  simp only [zero_mul, AddChar.map_zero_eq_one, smul_eq_mul, hzero,
    Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.inv_re, Complex.inv_im]
  norm_num [Complex.normSq] at *
  linarith

set_option maxHeartbeats 400000 in
-- The nine residue cases expand the complex phase products.
private lemma generator_residual (A : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (k : ZMod 9) :
    bispectrum (targetSpectrum A u) k 1 - bispectrum (sourceSpectrum A) k 1 =
      if k = 1 ∨ k = 7 then conj u - 1 else if k = 4 then u ^ 2 - 1 else 0 := by
  have hunit := unit_mul_conj u hu
  rcases nine_cases k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num (config := { decide := true, congrConsts := false })
      [bispectrum, sourceSpectrum, targetSpectrum, blockPhase, map_mul, pow_two]
    <;> first
      | (ring; done)
      | linear_combination (A : ℂ) * hunit

set_option maxHeartbeats 400000 in
-- The nine residue cases expand the complex phase products.
private lemma zero_residual (A : ℝ) (u : ℂ) (hu : ‖u‖ = 1) (k : ZMod 9) :
    bispectrum (targetSpectrum A u) 0 k = bispectrum (sourceSpectrum A) 0 k := by
  have hunit := unit_mul_conj u hu
  rcases nine_cases k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num (config := { decide := true, congrConsts := false })
      [bispectrum, sourceSpectrum, targetSpectrum, blockPhase, map_mul]
    <;> first
      | (ring; done)
      | (solve | linear_combination (2 * (A : ℂ) + 7) * hunit)
      | linear_combination (2 * (A : ℂ) + 7) * (A : ℂ) ^ 2 * hunit

private lemma cube_separation (u z : ℂ) (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (hz3 : z ^ 3 = 1) : ‖u ^ 3 - 1‖ ≤ 3 * ‖u - z‖ := by
  simpa [hz3] using
    D5.S3.AnalyticClosure.ComplexPowerDifference.norm_pow_sub_pow_le
      u z 3 1 (by norm_num) hu.le hz.le

private lemma translation_lower (A : ℝ) (hA : 1 ≤ A) (u : ℂ) (hu : ‖u‖ = 1)
    (t : ZMod 9) :
    A ^ 2 * ‖u ^ 3 - 1‖ ^ 2 / 81 ≤
      countingError (sourceSignal A) (targetSignal A u) t := by
  let z := ZMod.stdAddChar (-(3 * t))
  have hz : ‖z‖ = 1 := AddChar.norm_apply _ _
  have hz3 : z ^ 3 = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have ht : 3 • (-(3 * t)) = (0 : ZMod 9) := by
      rw [nsmul_eq_mul]
      calc
        _ = (9 : ZMod 9) * (-t) := by ring
        _ = 0 := by rw [show (9 : ZMod 9) = 0 from rfl]; exact zero_mul _
    rw [ht, AddChar.map_zero_eq_one]
  have hc := cube_separation u z hu hz hz3
  have hp := cyclic_parseval (fun x => targetSignal A u x - sourceSignal A (x - t))
  rw [Fintype.expect_eq_sum_div_card, ZMod.card] at hp
  change countingError (sourceSignal A) (targetSignal A u) t = _ at hp
  have hcoef : ZMod.dft (fun x => targetSignal A u x - sourceSignal A (x - t)) 3 =
      (A : ℂ) * (u - z) := by
    change (ZMod.dft ((targetSignal A u) - (fun x => sourceSignal A (x - t)))) 3 = _
    have hd := congr_fun ((ZMod.dft (N := 9) (E := ℂ)).map_sub
      (targetSignal A u) (fun x => sourceSignal A (x - t))) (3 : ZMod 9)
    calc
      _ = ZMod.dft (targetSignal A u) 3 - ZMod.dft (fun x => sourceSignal A (x - t)) 3 := hd
      _ = _ := by
        rw [dft_translation]
        simp only [sourceSignal, targetSignal, LinearEquiv.apply_symm_apply]
        change targetSpectrum A u 3 - z * sourceSpectrum A 3 = _
        change (A : ℂ) * u - z * (A : ℂ) = _
        ring
  have hs := single_le_sum (fun k (_ : k ∈ (univ : Finset (ZMod 9))) =>
    sq_nonneg ‖ZMod.dft (fun x => targetSignal A u x - sourceSignal A (x - t)) k‖)
    (mem_univ (3 : ZMod 9))
  rw [hcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ A)] at hs
  have hc2 : ‖u ^ 3 - 1‖ ^ 2 ≤ 9 * ‖u - z‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hc 2
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hc2 (sq_nonneg A)
  rw [hp]
  nlinarith only [hs, hh]

/-- The complete parameter-family properties concern actual inverse DFT signals. -/
structure FamilyProperties (A : ℝ) (u : ℂ) (J : ZMod 9 → ℂ) : Prop where
  source_dft : ZMod.dft (sourceSignal A) = sourceSpectrum A
  target_dft : ZMod.dft (ZMod.dft.symm J) = J
  source_real : ∀ x, (sourceSignal A x).im = 0
  target_real : ∀ x, (ZMod.dft.symm J x).im = 0
  source_positive : ∀ x, (1 : ℝ) / 9 ≤ (sourceSignal A x).re
  target_positive : ∀ x, (1 : ℝ) / 9 ≤ (ZMod.dft.symm J x).re
  calibration : sourceSpectrum A 0 = J 0
  dc_value : sourceSpectrum A 0 = (2 * A + 7 : ℝ)
  magnitude : ∀ k, ‖J k‖ = ‖sourceSpectrum A k‖
  spectral_lower : ∀ k, 1 ≤ ‖sourceSpectrum A k‖
  dc_dominance : ∀ k, ‖sourceSpectrum A k‖ ≤ ‖sourceSpectrum A 0‖
  dc_margin : ‖sourceSpectrum A 0‖ - ∑ k ∈ (univ : Finset (ZMod 9)).erase 0,
    ‖sourceSpectrum A k‖ = 1
  zero_row : ∀ k, bispectrum (J) 0 k = bispectrum (sourceSpectrum A) 0 k
  generator_signed : ∀ k,
    bispectrum (J) k 1 - bispectrum (sourceSpectrum A) k 1 =
      if k = 1 ∨ k = 7 then conj u - 1 else if k = 4 then u ^ 2 - 1 else 0
  generator_bound : ∀ k,
    ‖bispectrum (J) k 1 - bispectrum (sourceSpectrum A) k 1‖ ≤
      max ‖u - 1‖ ‖u ^ 2 - 1‖
  translation_separation : ∀ t,
    A ^ 2 * ‖u ^ 3 - 1‖ ^ 2 / 81 ≤ countingError (sourceSignal A) (ZMod.dft.symm J) t
  omitted_entry : bispectrum (J) 3 3 - bispectrum (sourceSpectrum A) 3 3 =
    (A : ℂ) ^ 3 * (u ^ 3 - 1)

/-- Unit block phases have bounded generator observations but amplified translation separation. -/
theorem parameter_family (A : ℝ) (hA : 1 ≤ A) (u : ℂ) (hu : ‖u‖ = 1) :
    FamilyProperties A u (targetSpectrum A u) := by
  refine ⟨LinearEquiv.apply_symm_apply _ _, LinearEquiv.apply_symm_apply _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, zero_residual A u hu,
    generator_residual A u hu, ?_, translation_lower A hA u hu, ?_⟩
  · exact inverse_real _ (fun k => (hermitian A u k).1)
  · exact inverse_real _ (fun k => (hermitian A u k).2)
  · exact inverse_lower A hA _ (by simp [sourceSpectrum]) (fun _ => rfl)
  · exact inverse_lower A hA _
      (by norm_num (config := { decide := true })
          [Fin.ext_iff, targetSpectrum, sourceSpectrum, blockPhase])
      (fun k => (spectrum_norm A hA u hu k).1)
  · norm_num (config := { decide := true })
      [Fin.ext_iff, Fin.val_add, Fin.val_neg, sourceSpectrum, targetSpectrum, blockPhase]
  · simp [sourceSpectrum]
  · exact fun k => (spectrum_norm A hA u hu k).1
  · exact fun k => (spectrum_norm A hA u hu k).2.1
  · exact fun k => (spectrum_norm A hA u hu k).2.2
  · simp_rw [source_norm A hA]
    rw [univ_nine]
    norm_num (config := { decide := true })
    ring
  · intro k
    rw [generator_residual A u hu k]
    split_ifs
    · have h : ‖conj u - 1‖ = ‖u - 1‖ := by
        simpa only [map_sub, map_one] using Complex.norm_conj (u - 1)
      rw [h]
      exact le_max_left _ _
    · exact le_max_right _ _
    · simp only [norm_zero]
      exact le_trans (norm_nonneg _) (le_max_left _ _)
  · norm_num (config := { decide := true })
      [Fin.ext_iff, Fin.val_add, bispectrum, targetSpectrum, sourceSpectrum, blockPhase, map_mul]
    ring

/-- A rational point of the unit circle, with a cubic defect separated from zero. -/
def rationalPhase : ℂ := ⟨255 / 257, 32 / 257⟩

def observationTolerance : ℝ := 64 / 257

set_option maxHeartbeats 400000 in
-- Exact rational complex powers require this arithmetic budget.
private lemma rational_estimates : ‖rationalPhase‖ = 1 ∧
    max ‖rationalPhase - 1‖ ‖rationalPhase ^ 2 - 1‖ ≤ observationTolerance ∧
    (1 : ℝ) / 3 < ‖rationalPhase ^ 3 - 1‖ ∧
    0 < observationTolerance ∧ observationTolerance < 1 / 4 := by
  have hn : ‖rationalPhase‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [rationalPhase, Complex.normSq]
  have h1 : ‖rationalPhase - 1‖ ≤ observationTolerance := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num [observationTolerance])).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [rationalPhase, observationTolerance, Complex.normSq]
  have h2 : ‖rationalPhase ^ 2 - 1‖ = observationTolerance := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num [observationTolerance])).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [rationalPhase, observationTolerance, Complex.normSq, pow_two,
      Complex.mul_re, Complex.mul_im]
  have h3 : (1 : ℝ) / 3 < ‖rationalPhase ^ 3 - 1‖ := by
    have h := Complex.abs_im_le_norm (rationalPhase ^ 3 - 1)
    change |(rationalPhase ^ 3 - 1).im| ≤ ‖rationalPhase ^ 3 - 1‖ at h
    have hi : |(rationalPhase ^ 3 - 1).im| = 6209632 / 16974593 := by
      norm_num [rationalPhase, pow_succ, Complex.mul_re, Complex.mul_im]
    rw [hi] at h
    linarith
  exact ⟨hn, max_le h1 h2.le, h3, by norm_num [observationTolerance],
    by norm_num [observationTolerance]⟩

/-- A single finite constant is required to work for every calibrated positive source. -/
def claim : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ZMod 9 → ℂ,
  (∀ x, (f x).im = 0 ∧ (1 : ℝ) / 9 ≤ (f x).re) →
  (∀ x, (g x).im = 0 ∧ (1 : ℝ) / 9 ≤ (g x).re) →
  ZMod.dft f 0 = ZMod.dft g 0 →
  (∀ k, ‖ZMod.dft g k‖ = ‖ZMod.dft f k‖ ∧ 1 ≤ ‖ZMod.dft f k‖ ∧
    ‖ZMod.dft f k‖ ≤ ‖ZMod.dft f 0‖) →
  (∀ k, bispectrum (ZMod.dft g) 0 k = bispectrum (ZMod.dft f) 0 k) →
  (∀ k, ‖bispectrum (ZMod.dft g) k 1 - bispectrum (ZMod.dft f) k 1‖ ≤
    observationTolerance) →
  ∃ t : ZMod 9, countingError f g t ≤ C ^ 2 * observationTolerance ^ 2

private lemma rational_obstruction (C : ℝ) (hC : 0 ≤ C) :
    FamilyProperties (27 * (C + 1)) rationalPhase
      (targetSpectrum (27 * (C + 1)) rationalPhase) ∧
    (∀ k, ‖bispectrum (targetSpectrum (27 * (C + 1)) rationalPhase) k 1 -
      bispectrum (sourceSpectrum (27 * (C + 1))) k 1‖ ≤ observationTolerance) ∧
    ∀ t : ZMod 9, C ^ 2 * observationTolerance ^ 2 <
      countingError (sourceSignal (27 * (C + 1)))
        (targetSignal (27 * (C + 1)) rationalPhase) t := by
  have hA : 1 ≤ 27 * (C + 1) := by linarith
  obtain ⟨hu, hobserve, hcubic, hepos, hesmall⟩ := rational_estimates
  have hp := parameter_family (27 * (C + 1)) hA rationalPhase hu
  refine ⟨hp, fun k => (hp.generator_bound k).trans hobserve, fun t => ?_⟩
  have hsep := hp.translation_separation t
  change (27 * (C + 1)) ^ 2 * ‖rationalPhase ^ 3 - 1‖ ^ 2 / 81 ≤
    countingError (sourceSignal (27 * (C + 1)))
      (targetSignal (27 * (C + 1)) rationalPhase) t at hsep
  have hs : (1 : ℝ) / 9 < ‖rationalPhase ^ 3 - 1‖ ^ 2 := by
    nlinarith [sq_nonneg (‖rationalPhase ^ 3 - 1‖ - 1 / 3)]
  have hmul := mul_lt_mul_of_pos_left hs (by positivity : 0 < (27 * (C + 1)) ^ 2)
  have he2 : observationTolerance ^ 2 < 1 := by nlinarith
  have hC2 := mul_le_mul_of_nonneg_left he2.le (sq_nonneg C)
  nlinarith

/-- No finite source-independent nonnegative counting-norm constant exists. -/
theorem result : ¬ claim := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨hp, hobserve, herror⟩ := rational_obstruction C hC
  obtain ⟨t, ht⟩ := hbound (sourceSignal (27 * (C + 1)))
    (targetSignal (27 * (C + 1)) rationalPhase)
    (fun x => ⟨hp.source_real x, hp.source_positive x⟩)
    (fun x => ⟨hp.target_real x, hp.target_positive x⟩)
    (by simp only [targetSignal]; rw [hp.source_dft, hp.target_dft]; exact hp.calibration)
    (by simp only [targetSignal]; rw [hp.source_dft, hp.target_dft]
        exact fun k => ⟨hp.magnitude k, hp.spectral_lower k, hp.dc_dominance k⟩)
    (by simp only [targetSignal]; rw [hp.source_dft, hp.target_dft]; exact hp.zero_row)
    (by simp only [targetSignal]; rw [hp.source_dft, hp.target_dft]; exact hobserve)
  exact (not_le_of_gt (herror t)) ht

end

#print axioms parameter_family
#print axioms result

end D5.S3.Fourier.GeneratorRowInstability
