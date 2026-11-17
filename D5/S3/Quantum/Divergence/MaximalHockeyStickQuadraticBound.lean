/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: The actual quadratic spectral value bounds every finite reverse preparation. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
import D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest

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

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticBound

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral quadratic value on the actual support of `A+B`. -/
def quadraticValue (A B : Matrix n n ℂ) : ℝ :=
  let S := A + B
  let T := normalize S (A - B)
  (S * (T * T)).trace.re

private theorem ratio_mass (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ((p - q) / (p + q)) * (p + q) = p - q ∧
      ((p - q) / (p + q)) ^ 2 * (p + q) = starPerspective p q := by
  by_cases h : p + q = 0
  · have hp0 : p = 0 := by linarith
    have hq0 : q = 0 := by linarith
    simp [hp0, hq0, starPerspective]
  · constructor
    · exact div_mul_cancel₀ _ h
    · unfold starPerspective
      field_simp

/-- Direct sum-of-squares bound for every actual finite CPTP reverse test.
The total mass may have a kernel; no optimizer or canonical optimality is
assumed. -/
theorem quadratic_value_le_test (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) {k : ℕ} (R : ReverseTest A B k) :
    quadraticValue A B ≤ R.starCost := by
  classical
  let S := A + B
  let K := spectralInverseSqrt S
  let P := spectralSupport S
  let mass : Fin k → ℝ := fun i => R.p i + R.q i
  let r : Fin k → ℝ := fun i => (R.p i - R.q i) / mass i
  let X : Fin k → Matrix n n ℂ := fun i => mass i • R.stateMatrix i
  let E : Fin k → Matrix n n ℂ := fun i => K * X i * K
  have hS : S.PosSemidef := hA.add hB
  obtain ⟨hroot, hK, hP, hPP, -, -, -, hnorm⟩ := spectral_sqrt_normalization S hS
  obtain ⟨hRK, hKR, hPK, -⟩ := spectral_sqrt_inverse_products S hS
  change Kᴴ = K at hK
  change Pᴴ = P at hP
  change P * P = P at hPP
  change K * S * K = P at hnorm
  change CFC.sqrt S * K = P at hRK
  change K * CFC.sqrt S = P at hKR
  have hstate (i : Fin k) : (R.stateMatrix i).PosSemidef :=
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (R.state i).2.1).posSemidef
  have hX (i : Fin k) : (X i).PosSemidef :=
    (hstate i).smul (add_nonneg (R.p_nonneg i) (R.q_nonneg i))
  have hsumX : ∑ i, X i = S := by
    simp only [X, mass, add_smul, Finset.sum_add_distrib, ReverseTest.stateMatrix]
    rw [R.prepares_left, R.prepares_right]
  have hXE (i : Fin k) : (E i).PosSemidef := by
    simpa only [E, hK] using (hX i).conjTranspose_mul_mul_same K
  have hsumE : ∑ i, E i = P := by
    simp only [E, ← Matrix.mul_sum, ← Matrix.sum_mul, hsumX]
    exact hnorm
  have hPle : P ≤ 1 := by
    have he : (1 - P)ᴴ * (1 - P) = 1 - P := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
      abel
    exact sub_nonneg.mp (he ▸ (Matrix.posSemidef_conjTranspose_mul_self (1 - P)).nonneg)
  have hratio (i : Fin k) := ratio_mass (R.p i) (R.q i) (R.p_nonneg i) (R.q_nonneg i)
  have hsumrX : ∑ i, r i • X i = A - B := by
    simp only [X, smul_smul]
    simp_rw [show ∀ i, r i * mass i = R.p i - R.q i from fun i => (hratio i).1]
    simp only [sub_smul, Finset.sum_sub_distrib, ReverseTest.stateMatrix]
    rw [R.prepares_left, R.prepares_right]
  have hM : ∑ i, r i • E i = normalize S (A - B) := by
    calc
      _ = K * (∑ i, r i • X i) * K := by
        simp only [E, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = normalize S (A - B) := by rw [hsumrX]; rfl
  have hbound := square_jensen_subunital E r hXE (hsumE ▸ hPle)
  rw [hM] at hbound
  have htrace (i : Fin k) : (S * E i).trace.re = mass i := by
    have hXiS : X i ≤ S := by
      rw [← hsumX]
      exact Finset.single_le_sum (fun j _ => (hX j).nonneg) (Finset.mem_univ i)
    obtain ⟨hPX, hXP⟩ := support_of_nonneg_le_smul S (X i) P hP
      (by
        obtain ⟨-, -, -, -, -, -, hPS, -⟩ := spectral_sqrt_normalization S hS
        exact hPS) (hX i) 1 (by simpa using hXiS)
    have hrec : reconstruct S (E i) = X i := by
      change CFC.sqrt S * (K * X i * K) * CFC.sqrt S = X i
      calc
        _ = P * X i * P := by
          simp only [← Matrix.mul_assoc, hRK]
          simp only [Matrix.mul_assoc, hKR]
        _ = X i := by rw [hPX, hXP]
    rw [← reconstruction_trace S (E i) hS, hrec]
    have htr : (R.stateMatrix i).trace = 1 := (R.state i).2.2
    simp only [X, Matrix.trace_smul, htr, Complex.real_smul, mul_one, Complex.ofReal_re]
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hS (Matrix.le_iff.mp hbound)
  change 0 ≤ (S * ((∑ i, r i ^ 2 • E i) -
    normalize S (A - B) * normalize S (A - B))).trace.re at h
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
  have he : (S * (∑ i, r i ^ 2 • E i)).trace.re = R.starCost := by
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, htrace]
    exact Finset.sum_congr rfl fun i _ => (hratio i).2
  rw [he] at h
  exact sub_nonneg.mp h

/-- The same bound for the genuine infimum over all finite reverse tests. -/
theorem quadratic_value_le_maximal (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (quadraticValue A B : EReal) ≤ maximalQuadratic A B := by
  apply le_sInf
  rintro z ⟨k, R, rfl⟩
  exact_mod_cast quadratic_value_le_test A B hA hB R

end D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticBound
