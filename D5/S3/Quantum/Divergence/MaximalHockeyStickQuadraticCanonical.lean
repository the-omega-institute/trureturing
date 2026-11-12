/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: An attained actual finite reverse-test formula for the quadratic generator. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticBound
import D5.S3.Quantum.Divergence.MaximalHockeyStickComponents
import D5.S3.Quantum.Divergence.MaximalHockeyStickOriginalPair

/-! The canonical spectral preparation attains the quadratic reverse-test infimum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
open D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticBound
open D5.S3.Quantum.Divergence.MaximalHockeyStickComponents
open D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticCanonical

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectral_test (S C : Matrix n n ℂ) (hS : S.PosSemidef)
    (hC : C.PosSemidef) (hC1 : C ≤ 1) :
    ∃ R : ReverseTest (reconstruct S C) (reconstruct S (1 - C)) (Fintype.card n),
      R.starCost = (S * (((2 : ℝ) • C - 1) * ((2 : ℝ) • C - 1))).trace.re ∧
      ∀ t : ℝ, R.hockey t = (reconstruct S C).trace.re -
        (S * canonicalOverlap C t).trace.re := by
  classical
  let hH := hC.isHermitian
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
  let E : n → Matrix n n ℂ := fun i => e (single i i 1)
  let G : n → Matrix n n ℂ := fun i => reconstruct S (E i)
  let x := hH.eigenvalues
  have hroot : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
    (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hE (i : n) : (E i).PosSemidef := by
    have hs : (single i i (1 : ℂ)).PosSemidef := by
      rw [← Matrix.diagonal_single]
      apply Matrix.PosSemidef.diagonal
      intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    change ((hH.eigenvectorUnitary : Matrix n n ℂ) * single i i 1 *
      (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ).PosSemidef
    exact hs.mul_mul_conjTranspose_same _
  have hG (i : n) : (G i).PosSemidef := by
    simpa only [G, reconstruct, hroot] using
      (hE i).conjTranspose_mul_mul_same (CFC.sqrt S)
  have hcf (f : ℝ → ℝ) : cfc f C = ∑ i, f (x i) • E i := by
    rw [hH.cfc_eq]
    change e (diagonal (fun i => (f (x i) : ℂ))) = _
    have hdiag : diagonal (fun i => (f (x i) : ℂ)) =
        ∑ i, (f (x i) : ℂ) • single i i (1 : ℂ) := by
      simp only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_single_eq_diagonal]
    rw [hdiag, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    exact Complex.coe_smul _ _
  have hcf1 : cfc (fun z : ℝ => 1 - z) C = 1 - C := by
    rw [cfc_sub _ _ C (by fun_prop) (by fun_prop),
      cfc_const 1 C hH.isSelfAdjoint, cfc_id' ℝ C hH.isSelfAdjoint]
    simp
  have hx (i : n) : 0 ≤ x i ∧ x i ≤ 1 := by
    refine ⟨hC.eigenvalues_nonneg i, ?_⟩
    have hnonneg : 0 ≤ cfc (fun z : ℝ => 1 - z) C := by
      rw [hcf1]
      exact sub_nonneg.mpr hC1
    have hs := (cfc_nonneg_iff _ C (by fun_prop) hH.isSelfAdjoint).mp hnonneg
    exact sub_nonneg.mp (hs _ (hH.eigenvalues_mem_spectrum_real i))
  obtain ⟨R, hcost, hprofile⟩ := reverse_test_from_components_profile G hG x hx
  have hleft : ∑ i, x i • G i = reconstruct S C := by
    rw [← cfc_id' ℝ C hH.isSelfAdjoint, hcf]
    simp only [G, reconstruct, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hright : ∑ i, (1 - x i) • G i = reconstruct S (1 - C) := by
    rw [← hcf1, hcf]
    simp only [G, reconstruct, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hsq : cfc (fun z : ℝ => (2 * z - 1) ^ 2) C =
      ((2 : ℝ) • C - 1) * ((2 : ℝ) • C - 1) := by
    have hz : cfc (fun z : ℝ => 2 * z - 1) C = (2 : ℝ) • C - 1 := by
      rw [cfc_sub _ _ C (by fun_prop) (by fun_prop),
        cfc_const_mul_id 2 C hH.isSelfAdjoint, cfc_const 1 C hH.isSelfAdjoint]
      simp
    rw [show (fun z : ℝ => (2 * z - 1) ^ 2) =
      (fun z : ℝ => (2 * z - 1) * (2 * z - 1)) by funext z; ring,
      cfc_mul _ _ C (by fun_prop) (by fun_prop), hz]
  have he : (S * (((2 : ℝ) • C - 1) * ((2 : ℝ) • C - 1))).trace.re =
      ∑ i, (2 * x i - 1) ^ 2 * (G i).trace.re := by
    rw [← hsq, hcf]
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (G i).trace = (S * E i).trace from reconstruction_trace S (E i) hS]
  refine ⟨
    { p := R.p
      q := R.q
      p_nonneg := R.p_nonneg
      q_nonneg := R.q_nonneg
      state := R.state
      prepares_left := R.prepares_left.trans hleft
      prepares_right := R.prepares_right.trans hright }, hcost.trans he.symm, ?_⟩
  intro t
  change R.hockey t = _
  have htrace (f : ℝ → ℝ) : (S * cfc f C).trace.re =
      ∑ i, f (x i) * (G i).trace.re := by
    rw [hcf]
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (G i).trace = (S * E i).trace from reconstruction_trace S (E i) hS]
  have hlefttrace : (reconstruct S C).trace.re = ∑ i, x i * (G i).trace.re := by
    rw [reconstruction_trace S C hS, ← cfc_id' ℝ C hH.isSelfAdjoint]
    exact htrace (fun z : ℝ => z)
  rw [hprofile, hlefttrace, canonicalOverlap, htrace, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hid : max (x i - t * (1 - x i)) 0 = x i - min (x i) (t * (1 - x i)) := by
    rcases le_total (x i) (t * (1 - x i)) with h | h
    · rw [min_eq_left h, sub_self, max_eq_right (sub_nonpos.mpr h)]
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  rw [hid]
  ring

/-- The canonical spectral test attains the actual finite-alphabet infimum
for the quadratic generator, including zero and singular pairs. -/
theorem quadratic_reverse_test_attained_profile (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ R : ReverseTest A B (Fintype.card n), R.starCost = quadraticValue A B ∧
      ∀ t : ℝ, R.hockey t = A.trace.re -
        ((A + B) * canonicalOverlap
          (MaximalHockeyStickSupport.normalize (A + B) A) t).trace.re := by
  let S := A + B
  let P := spectralSupport S
  let C := MaximalHockeyStickSupport.normalize S A
  have hS : S.PosSemidef := hA.add hB
  obtain ⟨hC, hCB, hsum⟩ := normalized_pair A B hA hB
  change C.PosSemidef at hC
  change C + MaximalHockeyStickSupport.normalize S B = P at hsum
  obtain ⟨hroot, hK, hP, hPP, hPR, hRP, hPS, -⟩ := spectral_sqrt_normalization S hS
  obtain ⟨hRK, hKR, hPK, hKP⟩ := spectral_sqrt_inverse_products S hS
  change Pᴴ = P at hP
  change P * P = P at hPP
  change P * spectralInverseSqrt S = spectralInverseSqrt S at hPK
  change spectralInverseSqrt S * P = spectralInverseSqrt S at hKP
  change P * S = S at hPS
  have hPle : P ≤ 1 := by
    have he : (1 - P)ᴴ * (1 - P) = 1 - P := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
      abel
    exact sub_nonneg.mp (he ▸ (Matrix.posSemidef_conjTranspose_mul_self (1 - P)).nonneg)
  have hCP : C ≤ P := by
    rw [← hsum]
    exact le_add_of_nonneg_right hCB.nonneg
  have hrecA' : reconstruct S C = A := by
    obtain ⟨hPA, hAP, -, -⟩ := pair_supported A B hA hB
    change CFC.sqrt S * (spectralInverseSqrt S * A * spectralInverseSqrt S) * CFC.sqrt S = A
    calc
      _ = spectralSupport S * A * spectralSupport S := by
        simp only [← Matrix.mul_assoc, hRK]
        simp only [Matrix.mul_assoc, hKR]
      _ = A := by rw [hPA, hAP]
  have hrecB : reconstruct S (1 - C) = B := by
    change CFC.sqrt S * (1 - C) * CFC.sqrt S = B
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, CFC.sqrt_mul_sqrt_self S hS.nonneg]
    change S - reconstruct S C = B
    rw [hrecA']
    dsimp only [S]
    abel
  obtain ⟨R, hcost, hprofile⟩ := spectral_test S C hS hC (hCP.trans hPle)
  have hPC : P * C = C := by
    simp only [C, MaximalHockeyStickSupport.normalize, ← Matrix.mul_assoc, hPK]
  have hCP' : C * P = C := by
    simp only [C, MaximalHockeyStickSupport.normalize, Matrix.mul_assoc, hKP]
  have hSP : S * P = S := by
    simpa only [Matrix.conjTranspose_mul, hS.isHermitian.eq, hP] using
      congrArg Matrix.conjTranspose hPS
  have hT : MaximalHockeyStickSupport.normalize S (A - B) = (2 : ℝ) • C - P := by
    have hd : MaximalHockeyStickSupport.normalize S B = P - C := by rw [← hsum]; abel
    simp only [MaximalHockeyStickSupport.normalize, Matrix.mul_sub, Matrix.sub_mul]
    change C - MaximalHockeyStickSupport.normalize S B = _
    rw [hd, two_smul ℝ]
    abel
  have hvalue : (S * (((2 : ℝ) • C - 1) * ((2 : ℝ) • C - 1))).trace.re =
      quadraticValue A B := by
    unfold quadraticValue
    change _ = (S * (MaximalHockeyStickSupport.normalize S (A - B) *
      MaximalHockeyStickSupport.normalize S (A - B))).trace.re
    rw [hT]
    congr 2
    simp only [two_smul ℝ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hPC, hCP', hSP, hPP]
  refine ⟨
    { p := R.p
      q := R.q
      p_nonneg := R.p_nonneg
      q_nonneg := R.q_nonneg
      state := R.state
      prepares_left := R.prepares_left.trans hrecA'
      prepares_right := R.prepares_right.trans hrecB }, hcost.trans hvalue, ?_⟩
  intro t
  change R.hockey t = _
  simpa only [hrecA'] using hprofile t

/-- The quadratic-cost projection of the actual spectral test with its exact
all-threshold profile. -/
theorem quadratic_reverse_test_attained (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ R : ReverseTest A B (Fintype.card n), R.starCost = quadraticValue A B := by
  obtain ⟨R, hc, -⟩ := quadratic_reverse_test_attained_profile A B hA hB
  exact ⟨R, hc⟩

/-- Exact formula for the genuine infimum, with no finite-value premise needed
for this bounded-perspective generator. -/
theorem maximal_quadratic_eq_value (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    maximalQuadratic A B = (quadraticValue A B : EReal) := by
  apply le_antisymm
  · obtain ⟨R, hR⟩ := quadratic_reverse_test_attained A B hA hB
    simpa only [hR] using maximal_quadratic_le_test R
  · exact quadratic_value_le_maximal A B hA hB

end D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticCanonical
