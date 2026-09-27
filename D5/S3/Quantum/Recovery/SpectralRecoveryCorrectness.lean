/- GID: D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/SpectralRecoveryCorrectness
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Any actual finite Kraus left inverse proves correctness of the computed spectral transpose recovery, yielding the full three-way finite-representation criterion. -/

import D5.S3.Quantum.Recovery.FiniteKrausReversibility
import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Correctness of the computed spectral recovery

Library-first: the left-inverse scalarity, finite-Kraus criterion, actual cfc
support, inverse square root, support action, and CPTP completion are reused.
Mathlib's `Commute.cfc_real` supplies the only functional-calculus commutation
step. This closes the bridge between existence of a finite Kraus inverse and
correctness of the specifically computed transpose candidate.

The proof constructs a Heisenberg observable map from an arbitrary represented
left inverse. Its intertwining is derived from the actual composite identity;
it is not an assumption that the computed recovery is correct. The conclusion
is the classical transpose-recovery criterion, with no novelty assertion.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
open D5.S3.Quantum.Recovery.FiniteKrausReversibility
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Foundation.FiniteStateChannel

variable {s t n d : Type*} [Fintype s] [DecidableEq s] [Fintype t]
  [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]

/-- The actual Heisenberg map of a represented recovery. -/
def leftInverseObservable (A : t → Matrix d n ℂ) (X : Matrix d d ℂ) :
    Matrix n n ℂ := ∑ b, (A b)ᴴ * X * A b

/-- The explicit formula of the previously constructed spectral CPTP candidate. -/
def spectralRecoveryAction (E : s → Matrix n d ℂ) (v : d) (X : Matrix n n ℂ) :
    Matrix d d ℂ :=
  let Q := ∑ a, E a * (E a)ᴴ
  let W := spectralInverseSqrt Q
  (∑ a, (E a)ᴴ * W * X * W * E a) +
    Matrix.trace ((1 - spectralSupport Q) * X) • Matrix.single v v 1

/-- Existence of any actual finite Kraus inverse makes the computed spectral candidate exact. -/
theorem computed_recovery_of_kraus_left_inverse (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1)
    (A : t → Matrix d n ℂ) (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (v : d) (X : Matrix d d ℂ) :
    spectralRecoveryAction E v (∑ a, E a * X * (E a)ᴴ) = X := by
  let Q := ∑ a, E a * (E a)ᴴ
  let P := spectralSupport Q
  let W := spectralInverseSqrt Q
  let Y := leftInverseObservable A X
  let NX := ∑ a, E a * X * (E a)ᴴ
  have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun a _ => (Matrix.posSemidef_self_mul_conjTranspose (E a)).nonneg)
  have hIntertwines (T : Matrix d d ℂ) (a : s) :
      leftInverseObservable A T * E a = E a * T := by
    let F : t × s → Matrix d d ℂ := fun p => A p.1 * E p.2
    have hF : ∀ Z : Matrix d d ℂ, (∑ p, F p * Z * (F p)ᴴ) = Z := by
      intro Z
      simpa only [F, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
        Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc] using hleft Z
    have hs (b : t) : A b * E a = (A b * E a) v v • (1 : Matrix d d ℂ) :=
      identity_kraus_scalar F hF v (b, a)
    have hterm (b : t) : (A b)ᴴ * T * (A b * E a) =
        (A b)ᴴ * (A b * E a) * T := by
      rw [hs b]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_assoc]
    calc
      _ = ∑ b, (A b)ᴴ * T * (A b * E a) := by
        simp only [leftInverseObservable, Matrix.sum_mul, Matrix.mul_assoc]
      _ = ∑ b, (A b)ᴴ * (A b * E a) * T := by simp_rw [hterm]
      _ = (∑ b, (A b)ᴴ * A b) * E a * T := by
        simp only [Matrix.sum_mul, Matrix.mul_assoc]
      _ = E a * T := by rw [hA, Matrix.one_mul]
  have hYE (a : s) : Y * E a = E a * X := hIntertwines X a
  have hEY (a : s) : (E a)ᴴ * Y = X * (E a)ᴴ := by
    have h := congrArg Matrix.conjTranspose
      (hIntertwines Xᴴ a)
    simpa only [Y, leftInverseObservable, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sum, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using h
  have hQY : Q * Y = NX := by
    simp only [Q, NX, Matrix.sum_mul, Matrix.mul_assoc, hEY]
  have hYQ : Y * Q = NX := by
    simp only [Q, NX, Matrix.mul_sum, ← Matrix.mul_assoc, hYE]
  have hcomm : Commute Q Y := hQY.trans hYQ.symm
  have hWY : W * Y = Y * W :=
    (hcomm.cfc_real (fun q : ℝ => (Real.sqrt q)⁻¹)).eq
  have hSandwich : W * Q * W = P := by
    change spectralInverseSqrt Q * Q * spectralInverseSqrt Q = spectralSupport Q
    have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Q) := by
      rw [continuousOn_iff_continuous_domRestrict]
      fun_prop
    have hmul (f g : ℝ → ℝ) :
        cfc f Q * cfc g Q = cfc (fun x => f x * g x) Q :=
      (cfc_mul f g Q (hcont f) (hcont g)).symm
    calc
      _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q * cfc (fun x : ℝ => x) Q *
          cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q := by
        rw [cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint]; rfl
      _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) Q := by
        rw [hmul, hmul]
      _ = spectralSupport Q := by
        apply cfc_congr
        intro x hx
        rw [hQ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        by_cases h : hQ.isHermitian.eigenvalues i = 0
        · simp [h]
        · have hx := hQ.eigenvalues_nonneg i
          have hs : Real.sqrt (hQ.isHermitian.eigenvalues i) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hx (Ne.symm h)))
          change (Real.sqrt (hQ.isHermitian.eigenvalues i))⁻¹ *
            hQ.isHermitian.eigenvalues i *
            (Real.sqrt (hQ.isHermitian.eigenvalues i))⁻¹ =
            (if hQ.isHermitian.eigenvalues i = 0 then 0 else 1)
          rw [if_neg h]
          field_simp [hs] <;> nlinarith [Real.sq_sqrt hx]
  have hWN : W * NX * W = P * Y := by
    calc
      _ = W * (Q * Y) * W := by rw [hQY]
      _ = (W * Q) * (Y * W) := by simp only [Matrix.mul_assoc]
      _ = (W * Q) * (W * Y) := by rw [← hWY]
      _ = (W * Q * W) * Y := by simp only [Matrix.mul_assoc]
      _ = P * Y := by rw [hSandwich]
  have hPE (a : s) : P * E a = E a := spectral_support_on_kraus E a
  have hPN : P * NX = NX := by
    simp only [NX, Matrix.mul_sum, ← Matrix.mul_assoc, hPE]
  have hz : (1 - P) * NX = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPN, sub_self]
  have hterm (a : s) : (E a)ᴴ * W * NX * W * E a = ((E a)ᴴ * E a) * X := by
    calc
      _ = (E a)ᴴ * (W * NX * W) * E a := by simp only [Matrix.mul_assoc]
      _ = (E a)ᴴ * (P * Y) * E a := by rw [hWN]
      _ = (E a)ᴴ * P * (Y * E a) := by simp only [Matrix.mul_assoc]
      _ = (E a)ᴴ * (P * E a) * X := by rw [hYE]; simp only [Matrix.mul_assoc]
      _ = ((E a)ᴴ * E a) * X := by rw [hPE]
  change (∑ a, (E a)ᴴ * W * NX * W * E a) +
    Matrix.trace ((1 - P) * NX) • Matrix.single v v 1 = X
  rw [hz, Matrix.trace_zero, zero_smul, add_zero]
  simp_rw [hterm]
  rw [← Matrix.sum_mul, hTP, Matrix.one_mul]

#print axioms computed_recovery_of_kraus_left_inverse

end D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
