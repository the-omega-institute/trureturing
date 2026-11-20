/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteRecovery
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recovery up to phase from a certified four-site marginal. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSitePencils
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteResidueLift

/-! The observed Gram supplies precisely the equations used by the residual rank proof. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteRecovery

open Matrix
open scoped Matrix
open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSFourSiteSextic
open PeriodicMPSFourSitePencils (swapBasis swapCoordinates swapCoordinates_inverse swapCoordinates_cyclic)
open PeriodicMPSFourSiteResidualFormula PeriodicMPSFourSiteResidualSystem
open PeriodicMPSFourSiteResidueLift
open UniformMPSExpectedDimensionRefutation (traceWord)

noncomputable section

def letters (A : Fin 2 → Bond) : Fin 6 → ℂ :=
  ![traceWord 2 2 4 A ![0, 0, 0, 0], traceWord 2 2 4 A ![1, 0, 0, 0],
    traceWord 2 2 4 A ![1, 1, 0, 0], traceWord 2 2 4 A ![1, 0, 1, 0],
    traceWord 2 2 4 A ![1, 1, 1, 0], traceWord 2 2 4 A ![1, 1, 1, 1]]

lemma letters_eq (A : Fin 2 → Bond) : letters A = necklaceTuple A := by
  let X := A 0
  let Y := A 1
  have fourth (M : Bond) : M * (M * (M * (M * 1))) = M ^ 4 := by
    simp [pow_succ, mul_assoc]
  funext i
  fin_cases i
  · change (X * (X * (X * (X * 1)))).trace = (X ^ 4).trace
    rw [fourth]
  · change (Y * (X * (X * (X * 1)))).trace = (X ^ 3 * Y).trace
    simp [Matrix.trace_mul_comm Y, pow_succ, mul_assoc]
  · change (Y * (Y * (X * (X * 1)))).trace = (X ^ 2 * Y ^ 2).trace
    rw [mul_one, ← mul_assoc Y Y, ← pow_two, ← pow_two, Matrix.trace_mul_comm]
  · change (Y * (X * (Y * (X * 1)))).trace = ((X * Y) ^ 2).trace
    rw [mul_one, ← mul_assoc Y X, ← pow_two]
    simp [pow_two, Matrix.trace_mul_comm Y, mul_assoc]
  · change (Y * (Y * (Y * (X * 1)))).trace = (X * Y ^ 3).trace
    rw [Matrix.trace_mul_comm X]
    simp [pow_succ, mul_assoc]
  · change (Y * (Y * (Y * (Y * 1)))).trace = (Y ^ 4).trace
    rw [fourth]

private def block (T : Matrix (Fin 3) (Fin 3) ℂ) (s : ℂ) :
    Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  fromBlocks T 0 0 (!![s] : Matrix (Fin 1) (Fin 1) ℂ)

private lemma block_mul (T U : Matrix (Fin 3) (Fin 3) ℂ) (s t : ℂ) :
    block T s * block U t = block (T * U) (s * t) := by
  unfold block
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  apply Matrix.ext
  intro i j
  simp [Matrix.mul_apply]

private lemma block_star (T : Matrix (Fin 3) (Fin 3) ℂ) (s : ℂ) :
    (block T s).map star = block (T.map star) (star s) := by
  apply Matrix.ext
  rintro (i | i) (j | j) <;>
    simp [block, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

private lemma block_smul (T : Matrix (Fin 3) (Fin 3) ℂ) (s c : ℂ) :
    c • block T s = block (c • T) (c * s) := by
  apply Matrix.ext
  rintro (i | i) (j | j) <;>
    simp [block, smul_eq_mul, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

private def inSwap (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  (swapCoordinates ℂ * M * swapBasis ℂ).submatrix finSumFinEquiv finSumFinEquiv

private lemma inSwap_mul (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    inSwap (M * N) = inSwap M * inSwap N := by
  unfold inSwap
  rw [Matrix.submatrix_mul_equiv]
  simp only [mul_assoc, ← mul_assoc (swapBasis ℂ) (swapCoordinates ℂ),
    (swapCoordinates_inverse ℂ).2, one_mul]

private lemma inSwap_smul (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    inSwap (c • M) = c • inSwap M := by
  simp only [inSwap, Matrix.mul_smul, Matrix.smul_mul]
  rfl

private lemma inSwap_injective : Function.Injective inSwap := by
  intro M N h
  have e : swapCoordinates ℂ * M * swapBasis ℂ =
      swapCoordinates ℂ * N * swapBasis ℂ := by
    apply Matrix.ext
    intro i j
    have h' := congrArg (fun Q => Q (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) h
    simpa only [inSwap, Matrix.submatrix_apply, Equiv.apply_symm_apply] using h'
  have e' := congrArg (fun P => swapBasis ℂ * P * swapCoordinates ℂ) e
  change swapBasis ℂ * ((swapCoordinates ℂ * M) * swapBasis ℂ) * swapCoordinates ℂ =
    swapBasis ℂ * ((swapCoordinates ℂ * N) * swapBasis ℂ) * swapCoordinates ℂ at e'
  simp only [← mul_assoc, (swapCoordinates_inverse ℂ).2, one_mul] at e'
  simpa only [mul_assoc, (swapCoordinates_inverse ℂ).2, mul_one] using e'

private lemma inSwap_flattening (A : Fin 2 → Bond) :
    inSwap (fourFlattening A) = block (tensorTriplet A) (singlet (tensorTriplet A)) := by
  unfold inSwap
  rw [fourFlattening_entries A]
  dsimp only
  rw [swapCoordinates_cyclic]
  apply Matrix.ext
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp only [block, tensorTriplet, singlet, triplet, Matrix.submatrix_apply, ← letters_eq A, letters,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] <;>
    try rfl
  change letters A 3 - letters A 2 = letters A 2 + letters A 3 - 2 * letters A 2
  ring

private lemma inSwap_star (M : Matrix (Fin 4) (Fin 4) ℂ) :
    inSwap (M.map star) = (inSwap M).map star := by
  have hb : (swapBasis ℂ).map star = swapBasis ℂ := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [swapBasis]
  have hc : (swapCoordinates ℂ).map star = swapCoordinates ℂ := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [swapCoordinates, map_div₀, map_ofNat]
  have he : (swapCoordinates ℂ * M * swapBasis ℂ).map star =
      swapCoordinates ℂ * M.map star * swapBasis ℂ := by
    change (starRingEnd ℂ).mapMatrix (swapCoordinates ℂ * M * swapBasis ℂ) = _
    rw [map_mul, map_mul]
    exact congrArg₂ (· * ·)
      (congrArg₂ (· * ·) hc (rfl : (starRingEnd ℂ).mapMatrix M = M.map star)) hb
  apply Matrix.ext
  intro i j
  exact congrArg (fun P : Matrix (Fin 4) (Fin 4) ℂ =>
    P (finSumFinEquiv i) (finSumFinEquiv j)) he.symm

def conjugateTensor (A : Fin 2 → Bond) : Fin 2 → Bond :=
  fun i => (A i).map star

private lemma conjugateTriplet (A : Fin 2 → Bond) :
    (tensorTriplet A).map star = tensorTriplet (conjugateTensor A) :=
  map_tensorTriplet (starRingEnd ℂ) A

private lemma singlet_star (M : Matrix (Fin 3) (Fin 3) ℂ) :
    singlet (M.map star) = star (singlet M) := by
  simp only [singlet, Matrix.map_apply, star_sub, star_mul, star_ofNat]
  ring

private lemma inSwap_conj (A : Fin 2 → Bond) :
    inSwap ((fourFlattening A).map star) =
      block (tensorTriplet (conjugateTensor A)) (singlet (tensorTriplet (conjugateTensor A))) := by
  rw [inSwap_star, inSwap_flattening, block_star, ← singlet_star, conjugateTriplet]

private lemma actualTripletEquation (A : Fin 2 → Bond) : tripletEquation (tensorTriplet A) = 0 := by
  unfold tensorTriplet
  rw [← letters_eq]
  exact tripletEquation_zero _ _ _ _ _ _ (sextic_actual A)

private lemma flatteningTranspose (A : Fin 2 → Bond) :
    (fourFlattening A).transpose = fourFlattening A := by
  rw [fourFlattening_entries]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma gramForwardReverse (A B : Fin 2 → Bond) (he : rawTwo B 0 = rawTwo A 0) :
    fourFlattening B * (fourFlattening B).map star =
      fourFlattening A * (fourFlattening A).map star ∧
    (fourFlattening B).map star * fourFlattening B =
      (fourFlattening A).map star * fourFlattening A := by
  have fw : fourFlattening B * (fourFlattening B).conjTranspose =
      fourFlattening A * (fourFlattening A).conjTranspose := by
    rw [fourFlattening_gram, fourFlattening_gram, he]
  have hconj (C : Fin 2 → Bond) : (fourFlattening C).conjTranspose =
      (fourFlattening C).map star := by
    rw [Matrix.conjTranspose, flatteningTranspose]
  rw [hconj, hconj] at fw
  have rev := congrArg Matrix.transpose fw
  rw [Matrix.transpose_mul, Matrix.transpose_mul, flatteningTranspose, flatteningTranspose] at rev
  have hstar (C : Fin 2 → Bond) : ((fourFlattening C).map star).transpose =
      (fourFlattening C).map star := by
    rw [← Matrix.transpose_map, flatteningTranspose]
  rw [hstar, hstar] at rev
  exact ⟨fw, rev⟩

private lemma block_eq {T U : Matrix (Fin 3) (Fin 3) ℂ} {s t : ℂ}
    (h : block T s = block U t) : T = U ∧ s = t := by
  constructor
  · exact (Matrix.fromBlocks_inj.mp h).1
  · exact congrArg (fun M => M (.inr 0) (.inr 0)) h

/-- This condition depends only on the six amplitudes and their conjugates. -/
def certificate (T U : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  T.det ≠ 0 ∧ U.det ≠ 0 ∧ singlet T * singlet U ≠ 0 ∧
    (cyclicMatrix (T * U) cyclicVector).det ≠ 0 ∧ (residualMinor T U).det ≠ 0

lemma certificate_iff (T U : Matrix (Fin 3) (Fin 3) ℂ) :
    certificate T U ↔ certificateValue T U ≠ 0 := by
  simp only [certificate, certificateValue, mul_ne_zero_iff]
  tauto

/-- On the locus where the coefficient certificate is nonzero, equality of the
adjacent two-site marginal determines the entire four-site amplitude up to phase. -/
theorem unitPhase_of_rawTwo_eq (A B : Fin 2 → Bond)
    (hgood : certificate (tensorTriplet A) (tensorTriplet (conjugateTensor A)))
    (he : rawTwo B 0 = rawTwo A 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ traceWord 2 2 4 B = c • traceWord 2 2 4 A := by
  let T := tensorTriplet A
  let U := tensorTriplet (conjugateTensor A)
  let T' := tensorTriplet B
  let U' := tensorTriplet (conjugateTensor B)
  obtain ⟨hT, hU, hS, hj, hdim⟩ := hgood
  obtain ⟨hF, hRev⟩ := gramForwardReverse A B he
  have first : block (T' * U') (singlet T' * singlet U') =
      block (T * U) (singlet T * singlet U) := by
    simpa only [inSwap_mul, inSwap_flattening, inSwap_conj, block_mul, T, U, T', U'] using
      congrArg inSwap hF
  have second : block (U' * T') (singlet U' * singlet T') =
      block (U * T) (singlet U * singlet T) := by
    simpa only [inSwap_mul, inSwap_flattening, inSwap_conj, block_mul, T, U, T', U'] using
      congrArg inSwap hRev
  have hbound := quotient_finrank_le_of_residualMinor T U hdim
  obtain ⟨c, hc⟩ := triplets_proportional T U T' U' (block_eq first).1 (block_eq second).1
    (block_eq first).2 hT hU hS hj (actualTripletEquation A)
    (actualTripletEquation (conjugateTensor A)) (actualTripletEquation B)
    (actualTripletEquation (conjugateTensor B)) hbound
  have hf : fourFlattening B = c • fourFlattening A := by
    apply inSwap_injective
    rw [inSwap_smul, inSwap_flattening, inSwap_flattening, block_smul]
    change block T' (singlet T') = block (c • T) (c * singlet T)
    have hSing : singlet (c • T) = c * singlet T := (singletLinear (R := ℂ)).map_smul c T
    rw [hc, hSing]
  have hG : rawTwo A 0 ≠ 0 := by
    intro hz
    have h := fourFlattening_gram A
    rw [hz] at h
    have hz0 : fourFlattening A * (fourFlattening A).conjTranspose = 0 := by
      apply Matrix.ext
      intro i j
      exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) h
    have hg : fourFlattening A * (fourFlattening A).map star =
        fourFlattening A * (fourFlattening A).conjTranspose := by
      rw [Matrix.conjTranspose, flatteningTranspose]
    rw [← hg] at hz0
    have hs := congrArg inSwap hz0
    rw [inSwap_mul, inSwap_flattening, inSwap_conj, block_mul] at hs
    have hw := congrArg (fun M => M (.inr 0) (.inr 0)) hs
    apply hS
    have hzero : inSwap 0 = 0 := by
      unfold inSwap
      rw [mul_zero, zero_mul]
      apply Matrix.ext
      intro i j
      rfl
    rw [hzero] at hw
    exact hw
  exact ⟨c, phase_of_proportional_flattening A B c hf he hG⟩


end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteRecovery
