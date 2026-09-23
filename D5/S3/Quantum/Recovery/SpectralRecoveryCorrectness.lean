/- GID: D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/SpectralRecoveryCorrectness
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Finite Kraus left inverses certify computed spectral recovery. -/

import D5.S3.Quantum.Recovery.FiniteKrausReversibility
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

private theorem observable_star (A : t → Matrix d n ℂ) (X : Matrix d d ℂ) :
    (leftInverseObservable A X)ᴴ = leftInverseObservable A Xᴴ := by
  simp only [leftInverseObservable, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- A genuine left inverse's observable map intertwines every original error. -/
theorem left_inverse_observable_intertwines (E : s → Matrix n d ℂ)
    (A : t → Matrix d n ℂ) (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (v : d) (X : Matrix d d ℂ) (a : s) :
    leftInverseObservable A X * E a = E a * X := by
  let F : t × s → Matrix d d ℂ := fun p => A p.1 * E p.2
  have hF : ∀ Y : Matrix d d ℂ, (∑ p, F p * Y * (F p)ᴴ) = Y := by
    intro Y
    simpa only [F, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc] using hleft Y
  have hs (b : t) : A b * E a = (A b * E a) v v • (1 : Matrix d d ℂ) :=
    identity_kraus_scalar F hF v (b, a)
  have hterm (b : t) : (A b)ᴴ * X * (A b * E a) =
      (A b)ᴴ * (A b * E a) * X := by
    rw [hs b]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
  calc
    _ = ∑ b, (A b)ᴴ * X * (A b * E a) := by
      simp only [leftInverseObservable, Matrix.sum_mul, Matrix.mul_assoc]
    _ = ∑ b, (A b)ᴴ * (A b * E a) * X := by simp_rw [hterm]
    _ = (∑ b, (A b)ᴴ * A b) * E a * X := by
      simp only [Matrix.sum_mul, Matrix.mul_assoc]
    _ = E a * X := by rw [hA, Matrix.one_mul]

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
  have hYE (a : s) : Y * E a = E a * X :=
    left_inverse_observable_intertwines E A hA hleft v X a
  have hEY (a : s) : (E a)ᴴ * Y = X * (E a)ᴴ := by
    have h := congrArg Matrix.conjTranspose
      (left_inverse_observable_intertwines E A hA hleft v Xᴴ a)
    simpa only [Matrix.conjTranspose_mul, observable_star,
      Matrix.conjTranspose_conjTranspose] using h
  have hQY : Q * Y = NX := by
    simp only [Q, NX, Matrix.sum_mul, Matrix.mul_assoc, hEY]
  have hYQ : Y * Q = NX := by
    simp only [Q, NX, Matrix.mul_sum, ← Matrix.mul_assoc, hYE]
  have hcomm : Commute Q Y := hQY.trans hYQ.symm
  have hWY : W * Y = Y * W :=
    (hcomm.cfc_real (fun q : ℝ => (Real.sqrt q)⁻¹)).eq
  have hWN : W * NX * W = P * Y := by
    calc
      _ = W * (Q * Y) * W := by rw [hQY]
      _ = (W * Q) * (Y * W) := by simp only [Matrix.mul_assoc]
      _ = (W * Q) * (W * Y) := by rw [← hWY]
      _ = (W * Q * W) * Y := by simp only [Matrix.mul_assoc]
      _ = P * Y := by rw [inverse_sqrt_sandwich Q hQ]
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
      _ = ((E a)ᴴ * E a) * X := by rw [hPE]; simp only [Matrix.mul_assoc]
  change (∑ a, (E a)ᴴ * W * NX * W * E a) +
    Matrix.trace ((1 - P) * NX) • Matrix.single v v 1 = X
  rw [hz, Matrix.trace_zero, zero_smul, add_zero]
  simp_rw [hterm]
  rw [← Matrix.sum_mul, hTP, Matrix.one_mul]

/-- Under the scalar criterion the same canonical channel has the computed formula and is an exact left inverse. -/
theorem canonical_spectral_left_inverse (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1) (v : d)
    (hE : ∀ a b, (E a)ᴴ * E b =
      (Matrix.trace ((E a)ᴴ * E b) / (Fintype.card d : ℂ)) • (1 : Matrix d d ℂ)) :
    ∃ recovery : QuantumChannel n d,
      (∀ Y : Matrix n n ℂ, CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)) = spectralRecoveryAction E v Y) ∧
      (∀ X : Matrix d d ℂ, CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix (∑ a, E a * X * (E a)ᴴ))) = X) := by
  obtain ⟨r, A, hA, hleft⟩ := (finite_kraus_left_inverse_iff E hTP v).mpr hE
  obtain ⟨recovery, hr⟩ := spectral_transpose_candidate E v
  have haction : ∀ Y : Matrix n n ℂ, CStarMatrix.ofMatrix.symm
      (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)) = spectralRecoveryAction E v Y := by
    intro Y
    simpa only [spectralRecoveryAction] using hr Y
  refine ⟨recovery, haction, fun X => ?_⟩
  rw [haction]
  exact computed_recovery_of_kraus_left_inverse E hTP A hA hleft v X

/-- The normalized-trace scalar criterion is equivalent to exactness of the computed spectral formula, completing the three-way finite-Kraus criterion. -/
theorem scalar_condition_iff_spectral_left_inverse (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1) (v : d) :
    (∀ a b, (E a)ᴴ * E b =
      (Matrix.trace ((E a)ᴴ * E b) / (Fintype.card d : ℂ)) • (1 : Matrix d d ℂ)) ↔
    (∀ X : Matrix d d ℂ, spectralRecoveryAction E v (∑ a, E a * X * (E a)ᴴ) = X) := by
  constructor
  · intro hE
    obtain ⟨r, A, hA, hleft⟩ := (finite_kraus_left_inverse_iff E hTP v).mpr hE
    exact computed_recovery_of_kraus_left_inverse E hTP A hA hleft v
  · intro hspec
    let Q := ∑ a, E a * (E a)ᴴ
    let P := spectralSupport Q
    let W := spectralInverseSqrt Q
    let K : s → Matrix d n ℂ := fun a => (E a)ᴴ * W
    let G : s ⊕ n → Matrix d n ℂ := completeKraus K P v
    have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
      (Finset.sum_nonneg fun a _ => (Matrix.posSemidef_self_mul_conjTranspose (E a)).nonneg)
    have hW : Wᴴ = W := spectral_inverse_sqrt_adjoint Q
    obtain ⟨hP, hPP⟩ := spectral_support_projection Q
    have hK : (∑ a, (K a)ᴴ * K a) = P := by
      calc
        _ = W * Q * W := by
          simp only [K, Q, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            hW, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        _ = P := inverse_sqrt_sandwich Q hQ
    have hG : (∑ b, (G b)ᴴ * G b) = 1 := complete_kraus_normalised K P v hP hPP hK
    have hGaction (Y : Matrix n n ℂ) :
        (∑ b, G b * Y * (G b)ᴴ) = spectralRecoveryAction E v Y := by
      change (∑ b, completeKraus K P v b * Y * (completeKraus K P v b)ᴴ) = _
      rw [complete_kraus_action K P v hP hPP]
      simp only [K, spectralRecoveryAction, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hW, Matrix.mul_assoc]
    have hleft : ∀ X : Matrix d d ℂ,
        (∑ b, G b * (∑ a, E a * X * (E a)ᴴ) * (G b)ᴴ) = X := by
      intro X
      rw [hGaction, hspec]
    exact fun a b => left_inverse_normalized_trace_condition E G hG hleft v a b

#print axioms left_inverse_observable_intertwines
#print axioms computed_recovery_of_kraus_left_inverse
#print axioms canonical_spectral_left_inverse
#print axioms scalar_condition_iff_spectral_left_inverse

end D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
