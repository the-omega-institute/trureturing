/- GID: D5/S3/Quantum/Recovery/SpectralTransposeRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/SpectralTransposeRecovery
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Spectral pseudoinverses construct normalized transpose recovery channels. -/

import D5.S3.Quantum.Recovery.KrausCompletion
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef

/-!
# A total spectral transpose-channel construction

The support and inverse square root are the existing Mathlib `cfc` applied to
explicit real functions. Thus they do not depend on a choice of eigenvectors.
The spectral theorem is used only to discharge nonnegativity on the spectrum.
Normalization reuses the canonical full-space Kraus completion. Nothing in this
file assumes exact recoverability; it constructs a CPTP candidate even when no
left inverse exists. Smoothness across a parameter family is not asserted.

The transpose/Petz construction belongs to Barnum--Knill and the earlier
recovery literature. Only the exact finite spectral construction is used here;
no approximate-fidelity theorem is imported.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.SpectralTransposeRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel

variable {n d s : Type*} [Fintype n] [DecidableEq n]
  [Fintype d] [DecidableEq d] [Fintype s]

/-- Nonzero spectral support, defined through the existing functional calculus. -/
def spectralSupport (Q : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else 1) Q

/-- The inverse square root is zero on the kernel. -/
def spectralInverseSqrt (Q : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q

private theorem finite_spectrum_continuous (Q : Matrix n n ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ Q) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

private theorem spectral_product (Q : Matrix n n ℂ) (f g : ℝ → ℝ) :
    cfc f Q * cfc g Q = cfc (fun x => f x * g x) Q :=
  (cfc_mul f g Q (finite_spectrum_continuous Q f)
    (finite_spectrum_continuous Q g)).symm

/-- The computed support is a Hermitian idempotent. -/
theorem spectral_support_projection (Q : Matrix n n ℂ) :
    (spectralSupport Q)ᴴ = spectralSupport Q ∧
      spectralSupport Q * spectralSupport Q = spectralSupport Q := by
  constructor
  · change star (cfc _ Q) = cfc _ Q
    exact (cfc_predicate _ Q : IsSelfAdjoint (cfc (fun x : ℝ =>
      if x = 0 then 0 else 1) Q)).star_eq
  · unfold spectralSupport
    rw [spectral_product]
    apply cfc_congr
    intro x hx
    split_ifs <;> simp

/-- Every Hermitian Q is supported in the computed nonzero spectral projection. -/
theorem spectral_support_mul (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) :
    spectralSupport Q * Q = Q := by
  calc
    _ = cfc (fun x : ℝ => if x = 0 then 0 else 1) Q *
        cfc (fun x : ℝ => x) Q := by rw [cfc_id' ℝ Q hQ.isSelfAdjoint]; rfl
    _ = cfc (fun x : ℝ => (if x = 0 then 0 else 1) * x) Q := spectral_product Q _ _
    _ = cfc (fun x : ℝ => x) Q := by
      apply cfc_congr
      intro x hx
      by_cases h : x = 0 <;> simp [h]
    _ = Q := cfc_id' ℝ Q hQ.isSelfAdjoint

private theorem scalar_inverse_sqrt (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · simp [h]
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hx (Ne.symm h)))
    rw [if_neg h]
    field_simp [hs] <;> nlinarith [Real.sq_sqrt hx]

/-- The pseudoinverse identity is proved for the computed spectral function, not supplied as an assumption. -/
theorem inverse_sqrt_sandwich (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    spectralInverseSqrt Q * Q * spectralInverseSqrt Q = spectralSupport Q := by
  calc
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q * cfc (fun x : ℝ => x) Q *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q := by
      rw [cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint]; rfl
    _ = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) Q := by
      rw [spectral_product, spectral_product]
    _ = spectralSupport Q := by
      apply cfc_congr
      intro x hx
      rw [hQ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact scalar_inverse_sqrt _ (hQ.eigenvalues_nonneg i)

private theorem output_gram_positive (E : s → Matrix n d ℂ) :
    (∑ a, E a * (E a)ᴴ).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun a _ =>
    (Matrix.posSemidef_self_mul_conjTranspose (E a)).nonneg

/-- The computed support contains every original Kraus image, including zero Kraus maps. -/
theorem spectral_support_on_kraus (E : s → Matrix n d ℂ) (a : s) :
    spectralSupport (∑ b, E b * (E b)ᴴ) * E a = E a := by
  let Q := ∑ b, E b * (E b)ᴴ
  let P := spectralSupport Q
  have hpq : P * Q = Q := spectral_support_mul Q (output_gram_positive E).isHermitian
  have hzero : (1 - P) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hpq, sub_self]
  have hsum : (∑ b, ((1 - P) * E b) * ((1 - P) * E b)ᴴ) = 0 := by
    calc
      _ = (1 - P) * Q * (1 - P)ᴴ := by
        simp only [Q, Matrix.conjTranspose_mul, Matrix.mul_sum,
          Matrix.sum_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hzero, Matrix.zero_mul]
  have hnonneg : ∀ b, (0 : Matrix n n ℂ) ≤
      ((1 - P) * E b) * ((1 - P) * E b)ᴴ :=
    fun b => (Matrix.posSemidef_self_mul_conjTranspose _).nonneg
  have hterms : ∀ b, ((1 - P) * E b) * ((1 - P) * E b)ᴴ = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum)
  have hz : ∀ b, ((1 - P) * E b)ᴴ = 0 := by
    intro b
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [Matrix.conjTranspose_conjTranspose] using hterms b
  have ha := Matrix.conjTranspose_eq_zero.mp (hz a)
  exact (sub_eq_zero.mp (by
    simpa only [Matrix.sub_mul, Matrix.one_mul] using ha)).symm

/-- Any finite CP branch, without division by its probability, supplies an explicit canonical CPTP recovery candidate. -/
theorem spectral_transpose_candidate (E : s → Matrix n d ℂ) (v : d) :
    let Q := ∑ a, E a * (E a)ᴴ
    let P := spectralSupport Q
    let W := spectralInverseSqrt Q
    ∃ recovery : QuantumChannel n d, ∀ X : Matrix n n ℂ,
      CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      (∑ a, (E a)ᴴ * W * X * W * E a) +
        Matrix.trace ((1 - P) * X) • Matrix.single v v 1 := by
  dsimp only
  let Q := ∑ a, E a * (E a)ᴴ
  let P := spectralSupport Q
  let W := spectralInverseSqrt Q
  have hQ : Q.PosSemidef := output_gram_positive E
  have hW : Wᴴ = W := by
    dsimp only [W, spectralInverseSqrt]
    change star (cfc _ Q) = cfc _ Q
    exact (cfc_predicate _ Q : IsSelfAdjoint
      (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q)).star_eq
  obtain ⟨hP, hPP⟩ := spectral_support_projection Q
  have hK : (∑ a, ((E a)ᴴ * W)ᴴ * ((E a)ᴴ * W)) = P := by
    calc
      _ = W * Q * W := by
        simp only [Q, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          hW, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = P := inverse_sqrt_sandwich Q hQ
  obtain ⟨recovery, hr⟩ := finite_kraus_quantum_channel
    (completeKraus (fun a => (E a)ᴴ * W) P v)
    (complete_kraus_normalised (fun a => (E a)ᴴ * W) P v hP hPP hK)
  refine ⟨recovery, fun X => ?_⟩
  rw [hr X, complete_kraus_action (fun a => (E a)ᴴ * W) P v hP hPP]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hW, Matrix.mul_assoc]

#print axioms spectral_support_projection
#print axioms spectral_support_mul
#print axioms inverse_sqrt_sandwich
#print axioms spectral_support_on_kraus
#print axioms spectral_transpose_candidate

end D5.S3.Quantum.Recovery.SpectralTransposeRecovery
