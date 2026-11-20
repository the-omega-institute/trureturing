/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantShiftedTheta
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantShiftedTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact discriminant theta inversion with a Gram-linear vector source. -/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Discriminant theta inversion with a vector source -/

open Matrix MeasureTheory
open scoped BigOperators Topology
open Filter Set

noncomputable section
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta
open D5.S3.Fourier

open MatrixGaussian
open private translatedGaussian translated_fourier translated_integrable
  translated_locally_summable translation_phase_norm
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil

private def modulatedTranslatedGaussian {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (b : ℂ) (s v : Fin r → ℝ) : C(Fin r → ℝ, ℂ) :=
  (⟨fun x => Complex.exp (2 * Real.pi * Complex.I * (v ⬝ᵥ (x+s) : ℝ)), by fun_prop⟩ :
      C(Fin r → ℝ, ℂ)) * translatedGaussian A b s

private theorem modulated_norm {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (b : ℂ) (s v x : Fin r → ℝ) :
    ‖modulatedTranslatedGaussian A b s v x‖ = ‖translatedGaussian A b s x‖ := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (v ⬝ᵥ (x+s) : ℝ)) *
    translatedGaussian A b s x‖ = _
  rw [norm_mul, translation_phase_norm, one_mul]

/-- A real source modulates the translated Gaussian Fourier transform. The
translation character remains at the original frequency. -/
private theorem translated_gaussian_fourier_real_source {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re)
    (s v w : Fin r → ℝ) :
    (∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      modulatedTranslatedGaussian A b s v x) =
      Complex.exp (2 * Real.pi * Complex.I * (w ⬝ᵥ s : ℝ)) *
        ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ (w-v) : ℂ))) := by
  have hp (x : Fin r → ℝ) :
      Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
          modulatedTranslatedGaussian A b s v x =
        Complex.exp (2 * Real.pi * Complex.I * (v ⬝ᵥ s : ℝ)) *
          (Complex.exp (-2 * Real.pi * Complex.I * ((w-v) ⬝ᵥ x : ℝ)) *
            translatedGaussian A b s x) := by
    change Complex.exp (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      (Complex.exp (2 * Real.pi * Complex.I * (v ⬝ᵥ (x+s) : ℝ)) *
        translatedGaussian A b s x) = _
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    rw [dotProduct_add, sub_dotProduct]
    push_cast
    ring
  simp_rw [hp]
  rw [integral_const_mul, translated_fourier A hA b hb s (w-v), ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  rw [sub_dotProduct]
  push_cast
  ring

/-- Poisson summation for the translated Gaussian with a real linear source.
The dual Gaussian is centered at the source and the phase uses the original
integer Fourier index. -/
private theorem translated_gaussian_poisson_real_source {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef) (b : ℂ) (hb : 0 < b.re)
    (s v : Fin r → ℝ) :
    (∑' n : Fin r → ℤ, modulatedTranslatedGaussian A b s v (fun i => (n i : ℝ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        ∑' k : Fin r → ℤ,
          Complex.exp (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
            Complex.exp (-Real.pi / b * (quadratic A⁻¹ ((fun i => (k i : ℝ))-v) : ℂ)) := by
  let F := modulatedTranslatedGaussian A b s v
  have hF (x : Fin r → ℝ) : ‖F x‖ = ‖translatedGaussian A b s x‖ :=
    modulated_norm A b s v x
  have hi : Integrable F := by
    apply (integrable_norm_iff (F.continuous.aestronglyMeasurable)).mp
    simpa only [hF] using (translated_integrable A hA b hb s).norm
  have hloc (K : TopologicalSpace.Compacts (Fin r → ℝ)) :
      Summable (fun n : Fin r → ℤ =>
        ‖(F.comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖) := by
    refine (translated_locally_summable A hA b hb s K).congr ?_
    intro n
    rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
    congr with x
    exact (hF _).symm
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  let K : TopologicalSpace.Compacts (Fin r → ℝ) := ⟨{0}, isCompact_singleton⟩
  have hks : Summable (fun k : Fin r → ℤ =>
      ‖Complex.exp (-Real.pi / b * (quadratic A⁻¹ ((fun i => (k i : ℝ))-v) : ℂ))‖) := by
    refine (translated_locally_summable A⁻¹ hA.inv b⁻¹ hbi (-v) K).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun k => ?_)
    have hh := ContinuousMap.norm_coe_le_norm
      (((translatedGaussian A⁻¹ b⁻¹ (-v)).comp
        (ContinuousMap.addRight (fun i => (k i : ℝ)))).restrict K) ⟨0, by simp [K]⟩
    change ‖gaussianMap A⁻¹ b⁻¹ ((0 + (fun i => (k i : ℝ))) + -v)‖ ≤ _ at hh
    simpa [gaussianMap, sub_eq_add_neg, div_eq_mul_inv, neg_mul] using hh
  have hs : Summable (fun k : Fin r → ℤ =>
      Complex.exp (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
        Complex.exp (-Real.pi / b * (quadratic A⁻¹ ((fun i => (k i : ℝ))-v) : ℂ))) :=
    Summable.of_norm (by simpa only [norm_mul, translation_phase_norm, one_mul] using hks)
  have hFT (k : Fin r → ℤ) :=
    translated_gaussian_fourier_real_source A hA b hb s v (fun i => (k i : ℝ))
  have hsf := hs.mul_left ((Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2))
  have hp := CoordinatePoisson.tsum_eq_tsum_integral hi hloc
    (hsf.congr (fun k => by simpa only [F, mul_left_comm, dotProduct] using (hFT k).symm))
  calc
    _ = ∑' k : Fin r → ℤ, ∫ x : Fin r → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i, (k i : ℝ) * x i : ℝ)) * F x := hp
    _ = ∑' k : Fin r → ℤ, (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        (Complex.exp (2 * Real.pi * Complex.I * ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
          Complex.exp (-Real.pi / b * (quadratic A⁻¹ ((fun i => (k i : ℝ))-v) : ℂ))) := by
      apply tsum_congr
      intro k
      simpa only [F, dotProduct, mul_left_comm] using hFT k
    _ = _ := tsum_mul_left

end D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta

namespace D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta
open D5.S3.Fourier.MatrixGaussian
open Matrix Complex

/-- The transformed quadratic term for the real source in the shifted
discriminant theta sum. -/
private theorem shifted_dual_quadratic {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hAs : A.IsSymm) (hA : IsUnit A.det) (k v : Fin r → ℝ) :
    quadratic A⁻¹ (k - A *ᵥ v) =
      quadratic A⁻¹ k - 2 * (k ⬝ᵥ v) + quadratic A v := by
  have hAv : A⁻¹ *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, one_mulVec]
  have hAk : A *ᵥ (A⁻¹ *ᵥ k) = k := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, one_mulVec]
  have hcross : (A *ᵥ v) ⬝ᵥ (A⁻¹ *ᵥ k) = k ⬝ᵥ v := by
    rw [dotProduct_comm (A *ᵥ v)]
    have hs := dotProduct_transpose_mulVec A (A⁻¹ *ᵥ k) v
    rw [hAs, hAk, dotProduct_comm v] at hs
    exact hs
  unfold quadratic
  rw [mulVec_sub, hAv, sub_dotProduct, dotProduct_sub, dotProduct_sub, hcross,
    dotProduct_comm (A *ᵥ v) v]
  ring

/-- The dual Fourier summand factors into the source multiplier and the
dual theta summand. The cross term carries the sign and factor of two
needed by the original charge source. -/
private theorem shifted_theta_fourier_exponent {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hAs : A.IsSymm) (hA : IsUnit A.det) {τ : ℂ} (hτ : τ ≠ 0) (k v : Fin r → ℝ) :
    Complex.exp (-Real.pi / (-Complex.I * τ) *
      (quadratic A⁻¹ (k - A *ᵥ v) : ℂ)) =
    Complex.exp (-Real.pi * Complex.I / τ * (quadratic A v : ℂ)) *
      Complex.exp (Real.pi * Complex.I * (-1 / τ) * (quadratic A⁻¹ k : ℂ) +
        2 * Real.pi * Complex.I / τ * (k ⬝ᵥ v : ℝ)) := by
  have hs : (-Real.pi : ℂ) / (-Complex.I * τ) =
      -Real.pi * Complex.I / τ := by
    field_simp [hτ, Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  rw [shifted_dual_quadratic A hAs hA, hs, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta


namespace D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta
open D5.S3.Fourier
open MatrixGaussian Complex
open private translatedGaussian translation_phase_norm
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil

/-- The shifted theta transform before reindexing the dual lattice into its
discriminant sectors. The source coordinate on the dual side is divided by τ. -/
private theorem shifted_theta_poisson_real_source {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (hAs : A.IsSymm) (hA : A.PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) (s v : Fin r → ℝ) :
    (∑' n : Fin r → ℤ,
      Complex.exp (Real.pi * Complex.I * τ *
        (quadratic A ((fun i => (n i : ℝ)) + s) : ℂ) +
        2 * Real.pi * Complex.I * ((A *ᵥ v) ⬝ᵥ ((fun i => (n i : ℝ)) + s) : ℝ))) =
      ((Real.sqrt A.det : ℂ)⁻¹ * (-Complex.I * τ) ^ (-(r : ℂ) / 2)) *
      Complex.exp (-Real.pi * Complex.I / τ * (quadratic A v : ℂ)) *
      ∑' k : Fin r → ℤ,
        Complex.exp (2 * Real.pi * Complex.I *
          ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) *
        Complex.exp (Real.pi * Complex.I * (-1 / τ) *
          (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ) +
          2 * Real.pi * Complex.I / τ * ((fun i => (k i : ℝ)) ⬝ᵥ v : ℝ)) := by
  have hb : 0 < (-Complex.I * τ).re := by simpa using hτ
  have hτ0 : τ ≠ 0 := by intro he; simp [he] at hτ
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have h := translated_gaussian_poisson_real_source A hA (-Complex.I * τ) hb s (A *ᵥ v)
  have hleft (n : Fin r → ℤ) :
      modulatedTranslatedGaussian A (-Complex.I * τ) s (A *ᵥ v) (fun i => (n i : ℝ)) =
      Complex.exp (Real.pi * Complex.I * τ *
        (quadratic A ((fun i => (n i : ℝ)) + s) : ℂ) +
        2 * Real.pi * Complex.I * ((A *ᵥ v) ⬝ᵥ ((fun i => (n i : ℝ)) + s) : ℝ)) := by
    change Complex.exp _ * (gaussianMap A (-Complex.I * τ) ((fun i => (n i : ℝ)) + s)) = _
    unfold gaussianMap
    simp only [ContinuousMap.coe_mk]
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [hleft, shifted_theta_fourier_exponent A hAs hunit hτ0] at h
  rw [h]
  simp_rw [mul_left_comm (Complex.exp (2 * Real.pi * Complex.I * _))]
  rw [tsum_mul_left]
  ring

end D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta

namespace D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta
open D5.S3.Fourier
open MatrixGaussian Complex

open private translatedGaussian translated_locally_summable translation_phase_norm shift_phase
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
open private cosetEquiv_apply inverse_quadratic_coset class_add class_representative class_gram
  shift_eq real_unit gramReal_symm cast_gram
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeDiscriminantTheta

private def realSourceTheta (D : LatticeData) (a : Discriminant D)
    (τ t : ℂ) (v : Fin D.rank → ℝ) : ℂ :=
  ∑' n : Charge D, Complex.exp
    (Real.pi * Complex.I * τ * (quadratic (gramReal D)
      ((fun i => (n i : ℝ)) + shift D (representative D a)) : ℂ) +
      2 * Real.pi * Complex.I * t *
        (((gramReal D) *ᵥ v) ⬝ᵥ ((fun i => (n i : ℝ)) + shift D (representative D a)) : ℝ))

/-- On a real source vector the exact Fourier inverse is a finite sum of
discriminant theta sectors with complex transformed source parameter. -/
private theorem real_source_sector_S (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) (v : Fin D.rank → ℝ) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    realSourceTheta D a τ 1 v =
      ((Real.sqrt (gramReal D).det : ℂ)⁻¹ * (-Complex.I * τ) ^ (-(D.rank : ℂ) / 2)) *
      Complex.exp (-Real.pi * Complex.I / τ * (quadratic (gramReal D) v : ℂ)) *
      ∑ c : Discriminant D, pairingCharacter D hD a c * realSourceTheta D c (-1 / τ) (1 / τ) v := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  let A := gramReal D
  let s := shift D (representative D a)
  let b := -Complex.I * τ
  let C := Complex.exp (-Real.pi * Complex.I / τ * (quadratic A v : ℂ))
  have hτ0 : τ ≠ 0 := by intro he; simp [he] at hτ
  have hb : 0 < b.re := by simpa [b] using hτ
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hbi : 0 < (b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb0)
  let J (k : Charge D) := Complex.exp
    (Real.pi * Complex.I * (-1 / τ) *
       (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ) +
      2 * Real.pi * Complex.I / τ * ((fun i => (k i : ℝ)) ⬝ᵥ v : ℝ))
  let U (k : Charge D) := Complex.exp (2 * Real.pi * Complex.I *
    ((fun i => (k i : ℝ)) ⬝ᵥ s : ℝ)) * J k
  let K : TopologicalSpace.Compacts (Fin D.rank → ℝ) := ⟨{0}, isCompact_singleton⟩
  have hks : Summable (fun k : Charge D =>
      ‖Complex.exp (-Real.pi / b * (quadratic A⁻¹ ((fun i => (k i : ℝ))-A *ᵥ v) : ℂ))‖) := by
    refine (translated_locally_summable A⁻¹ hD.inv b⁻¹ hbi (-(A *ᵥ v)) K).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun k => ?_)
    have hh := ContinuousMap.norm_coe_le_norm
      (((translatedGaussian A⁻¹ b⁻¹ (-(A *ᵥ v))).comp
        (ContinuousMap.addRight (fun i => (k i : ℝ)))).restrict K) ⟨0, by simp [K]⟩
    change ‖gaussianMap A⁻¹ b⁻¹ ((0 + (fun i => (k i : ℝ))) + -(A *ᵥ v))‖ ≤ _ at hh
    simpa [gaussianMap, sub_eq_add_neg, div_eq_mul_inv, neg_mul] using hh
  have hJ : Summable (fun k : Charge D => ‖J k‖) := by
    have h := hks.mul_left ‖C⁻¹‖
    refine h.congr fun k => ?_
    rw [show -Real.pi / b = -Real.pi / (-Complex.I * τ) from rfl,
      shifted_theta_fourier_exponent A (gramReal_symm D) (real_unit D hD) hτ0,
      ← show C = Complex.exp (-Real.pi * Complex.I / τ * (quadratic A v : ℂ)) from rfl,
      ← norm_mul, ← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]
  have hU : Summable U :=
    Summable.of_norm (by simpa only [U, norm_mul, translation_phase_norm, one_mul] using hJ)
  have hp := hU.comp_injective (cosetEquiv D hD).injective
  have hsplit :
      (∑' k : Charge D, U k) = ∑ c : Discriminant D,
        pairingCharacter D hD a c * realSourceTheta D c (-1 / τ) (1 / τ) v := by
    calc
      _ = ∑' p : Discriminant D × Charge D, U (cosetEquiv D hD p) :=
        ((cosetEquiv D hD).tsum_eq U).symm
      _ = ∑ c : Discriminant D, ∑' n : Charge D, U (cosetEquiv D hD (c,n)) := by
        simpa only [Function.comp_apply, tsum_fintype] using hp.tsum_prod
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        unfold realSourceTheta
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        have hLin : (fun i => ((representative D c + gramMap D n) i : ℝ)) ⬝ᵥ v =
            (A *ᵥ v) ⬝ᵥ ((fun i => (n i : ℝ)) + shift D (representative D c)) := by
          have hc : (fun i => ((representative D c + gramMap D n) i : ℝ)) =
              A *ᵥ ((fun i => (n i : ℝ)) + shift D (representative D c)) := by
            dsimp [A]
            rw [mulVec_add, shift_eq D hD, mulVec_mulVec,
              mul_nonsing_inv _ (real_unit D hD), one_mulVec, ← cast_gram]
            ext i
            simp [add_comm]
          rw [hc, dotProduct_comm (A *ᵥ _)]
          have hs : Aᵀ = A := gramReal_symm D
          simpa only [hs, dotProduct_comm (A *ᵥ v)] using
            dotProduct_transpose_mulVec A v ((fun i => (n i : ℝ)) + shift D (representative D c))
        dsimp only [U, s, J, realSourceTheta, A]
        rw [cosetEquiv_apply, shift_phase D hD, class_add, class_gram,
          class_representative, add_zero, inverse_quadratic_coset D hD, hLin]
        congr 2
        ring
  have hmain := shifted_theta_poisson_real_source A (gramReal_symm D) hD τ hτ s v
  change realSourceTheta D a τ 1 v = _
  rw [← hsplit]
  simpa only [U, J, C, A, s, realSourceTheta, mul_one] using hmain


/-- The complex bilinear extension of the real Gaussian quadratic form. -/
def sourceQuadratic {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (z : Fin r → ℂ) : ℂ :=
  z ⬝ᵥ (A.map Complex.ofReal) *ᵥ z

private def thetaTerm {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (τ : ℂ) (z : Fin r → ℂ) (x : Fin r → ℝ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * τ * (quadratic A x : ℂ) +
    2 * Real.pi * Complex.I * ((fun i => (↑((A *ᵥ x) i) : ℂ)) ⬝ᵥ z))

/-- The theta series on the indicated literal discriminant sector, with a
complex source coupled by the Gram bilinear form. -/
def shiftedTheta (D : LatticeData) (a : Discriminant D) (τ : ℂ) (z : Fin D.rank → ℂ) : ℂ :=
  ∑' n : Charge D, thetaTerm (gramReal D) τ z
    ((fun i => (n i : ℝ)) + shift D (representative D a))

private theorem sourceQuadratic_real {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (v : Fin r → ℝ) :
    sourceQuadratic A (fun i => (v i : ℂ)) = (quadratic A v : ℂ) := by
  simp [sourceQuadratic, quadratic, dotProduct, mulVec, Finset.mul_sum]

private theorem shiftedTheta_scalar_real (D : LatticeData) (a : Discriminant D) (τ t : ℂ)
    (v : Fin D.rank → ℝ) :
    shiftedTheta D a τ (t • fun i => (v i : ℂ)) = realSourceTheta D a τ t v := by
  apply tsum_congr
  intro n
  unfold thetaTerm
  rw [dotProduct_smul, smul_eq_mul]
  let x : Fin D.rank → ℝ := (fun i => (n i : ℝ)) + shift D (representative D a)
  have hx : ((fun i => (↑((gramReal D *ᵥ x) i) : ℂ)) ⬝ᵥ fun i => (v i : ℂ)) =
      ((gramReal D *ᵥ v ⬝ᵥ x : ℝ) : ℂ) := by
    change (Complex.ofRealHom ∘ (gramReal D *ᵥ x)) ⬝ᵥ (Complex.ofRealHom ∘ v) = _
    rw [← Complex.ofRealHom.map_dotProduct]
    change (↑((gramReal D *ᵥ x) ⬝ᵥ v) : ℂ) = _
    rw [dotProduct_comm (gramReal D *ᵥ x), ← dotProduct_transpose_mulVec,
      gramReal_symm D, dotProduct_comm x]
  change Complex.exp (_ + _ * (t * (((fun i => (↑((gramReal D *ᵥ x) i) : ℂ)) ⬝ᵥ _)))) = _
  rw [hx]
  congr 1
  ring

/-- Inverse source-coupled S transformation for a real vector. The translated
Poisson series is resolved over every discriminant class. -/
theorem shiftedTheta_real_S (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) (v : Fin D.rank → ℝ) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    shiftedTheta D a τ (fun i => (v i : ℂ)) =
      ((Real.sqrt (gramReal D).det : ℂ)⁻¹ * (-Complex.I * τ) ^ (-(D.rank : ℂ) / 2)) *
      Complex.exp (-Real.pi * Complex.I / τ * sourceQuadratic (gramReal D) (fun i => (v i : ℂ))) *
      ∑ c : Discriminant D, pairingCharacter D hD a c *
        shiftedTheta D c (-1 / τ) (τ⁻¹ • fun i => (v i : ℂ)) := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  have hl := shiftedTheta_scalar_real D a τ 1 v
  rw [one_smul] at hl
  rw [hl, sourceQuadratic_real]
  simp_rw [shiftedTheta_scalar_real]
  simpa only [one_div] using real_source_sector_S D hD a τ hτ v

private theorem thetaTerm_affine {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (τ t : ℂ) (v w : Fin r → ℂ) (x : Fin r → ℝ) :
    thetaTerm A τ (v + t • w) x =
      Complex.exp (Real.pi * Complex.I * τ * (quadratic A x : ℂ) +
        ∑ i, (x i : ℂ) *
          ((2 * Real.pi * Complex.I) * (((Aᵀ.map Complex.ofReal) *ᵥ v) i +
            t * (((Aᵀ.map Complex.ofReal) *ᵥ w) i)))) := by
  unfold thetaTerm
  have hcast : (fun i => (↑((A *ᵥ x) i) : ℂ)) =
      A.map Complex.ofReal *ᵥ (fun i => (x i : ℂ)) :=
    funext (Complex.ofRealHom.map_mulVec A x)
  rw [hcast, dotProduct_comm, ← dotProduct_transpose_mulVec]
  change Complex.exp (_ + _ * ((fun i => (x i : ℂ)) ⬝ᵥ
    (Aᵀ.map Complex.ofReal *ᵥ (v + t • w)))) = _
  rw [mulVec_add, mulVec_smul, dotProduct, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem affine_majorant {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (τ : ℂ) (hτ : 0 < τ.im) (s : Fin r → ℝ)
    (v w : Fin r → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ u : (Fin r → ℤ) → ℝ, Summable u ∧
      ∀ (n : Fin r → ℤ) (t : ℂ), ‖t‖ ≤ R →
        ‖thetaTerm A τ (v + t • w) ((fun i => (n i : ℝ)) + s)‖ ≤ u n := by
  obtain ⟨c, hc, hcoercive⟩ := exists_quadratic_lower_bound A hA
  let d := Real.pi * τ.im * c / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let B := Aᵀ.map Complex.ofReal
  let L (i : Fin r) : ℝ := ‖(2 * Real.pi * Complex.I : ℂ)‖ *
    (‖(B *ᵥ v) i‖ + R * ‖(B *ᵥ w) i‖)
  let M := ∑ i, L i ^ 2 / (4 * d)
  let b : ℂ := -Complex.I * τ / 2
  have hb : 0 < b.re := by simpa [b, Complex.div_re] using
    (show 0 < τ.im / 2 by positivity)
  let K : TopologicalSpace.Compacts (Fin r → ℝ) := ⟨{0}, isCompact_singleton⟩
  let u (n : Fin r → ℤ) := Real.exp M *
    ‖gaussianMap A b ((fun i => (n i : ℝ)) + s)‖
  refine ⟨u, ?_, ?_⟩
  · apply Summable.mul_left
    refine (translated_locally_summable A hA b hb s K).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    have hn := ContinuousMap.norm_coe_le_norm
      (((translatedGaussian A b s).comp
        (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K) ⟨0, by simp [K]⟩
    change ‖gaussianMap A b ((0 + (fun i => (n i : ℝ))) + s)‖ ≤ _ at hn
    simpa only [zero_add] using hn
  intro n t ht
  let x : Fin r → ℝ := (fun i => (n i : ℝ)) + s
  let a (i : Fin r) : ℂ := (2 * Real.pi * Complex.I) * ((B *ᵥ v) i + t * (B *ᵥ w) i)
  have ha (i : Fin r) : ‖a i‖ ≤ L i := by
    rw [show ‖a i‖ = ‖(2 * Real.pi * Complex.I : ℂ)‖ *
        ‖(B *ᵥ v) i + t * (B *ᵥ w) i‖ by simp only [a, norm_mul]]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have ht' : ‖t * (B *ᵥ w) i‖ ≤ R * ‖(B *ᵥ w) i‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    exact (norm_add_le _ _).trans (add_le_add_right ht' _)
  have hlinear : (∑ i, (x i : ℂ) * a i).re ≤ d * (∑ i, (x i) ^ 2) + M := by
    change Complex.reAddGroupHom (∑ i, (x i : ℂ) * a i) ≤ _
    rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    change (∑ i, ((x i : ℂ) * a i).re) ≤ ∑ i, (d * (x i) ^ 2 + L i ^ 2 / (4 * d))
    apply Finset.sum_le_sum
    intro i _
    have h₁ : ((x i : ℂ) * a i).re ≤ |x i| * L i := by
      calc
        _ ≤ ‖(x i : ℂ) * a i‖ := Complex.re_le_norm _
        _ = |x i| * ‖a i‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ _ := mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)
    have hd₀ : d ≠ 0 := hd.ne'
    have h₂ := mul_nonneg hd.le (sq_nonneg (|x i| - L i / (2 * d)))
    have h₃ : d * (|x i| - L i / (2 * d)) ^ 2 =
        d * |x i| ^ 2 - |x i| * L i + L i ^ 2 / (4 * d) := by
      field_simp
      ring
    rw [h₃, sq_abs] at h₂
    exact h₁.trans (by linarith)
  have hq : d * (∑ i, (x i) ^ 2) ≤ Real.pi * τ.im * quadratic A x / 2 := by
    have hh := mul_le_mul_of_nonneg_left (hcoercive x)
      (show 0 ≤ Real.pi * τ.im / 2 by positivity)
    dsimp [d]
    linarith only [hh]
  change ‖thetaTerm A τ (v + t • w) x‖ ≤ Real.exp M * ‖gaussianMap A b x‖
  rw [thetaTerm_affine, Complex.norm_exp, gaussianMap]
  simp only [ContinuousMap.coe_mk, Complex.norm_exp, ← Real.exp_add, Complex.add_re]
  apply Real.exp_le_exp.mpr
  have hmain : (Real.pi * Complex.I * τ * (quadratic A x : ℂ)).re =
      -Real.pi * τ.im * quadratic A x := by simp [Complex.mul_re, Complex.mul_im]
  have hgauss : (-Real.pi * b * (quadratic A x : ℂ)).re =
      -(Real.pi * τ.im * quadratic A x / 2) := by
    simp [b, Complex.mul_re, Complex.mul_im]
    ring
  rw [hmain, hgauss]
  change -Real.pi * τ.im * quadratic A x + (∑ i, (x i : ℂ) * a i).re ≤
    M + -(Real.pi * τ.im * quadratic A x / 2)
  linarith only [hlinear, hq]

private theorem shiftedTheta_affine_entire (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) (v w : Fin D.rank → ℂ) :
    Differentiable ℂ (fun t : ℂ => shiftedTheta D a τ (v + t • w)) := by
  intro t
  let R := ‖t‖ + 1
  obtain ⟨u, hu, hb⟩ := affine_majorant (gramReal D) hD τ hτ
    (shift D (representative D a)) v w R (by dsimp [R]; positivity)
  let F (n : Charge D) (t' : ℂ) := thetaTerm (gramReal D) τ (v + t' • w)
    ((fun i => (n i : ℝ)) + shift D (representative D a))
  have hd : DifferentiableOn ℂ (fun t' => ∑' n, F n t') (Metric.ball (0 : ℂ) R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu ?_ Metric.isOpen_ball ?_
    · intro n
      simp only [F, thetaTerm_affine]
      fun_prop
    · intro n t' ht'
      exact hb n t' (mem_ball_zero_iff.mp ht').le
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds
    (mem_ball_zero_iff.mpr (by dsimp [R]; linarith)))

/-- Complex-source theta inversion, obtained by analytic continuation along
the affine line joining the real source to its complex value. -/
theorem shiftedTheta_S (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) (z : Fin D.rank → ℂ) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    shiftedTheta D a τ z =
      ((Real.sqrt (gramReal D).det : ℂ)⁻¹ * (-Complex.I * τ) ^ (-(D.rank : ℂ) / 2)) *
      Complex.exp (-Real.pi * Complex.I / τ * sourceQuadratic (gramReal D) z) *
      ∑ c : Discriminant D, pairingCharacter D hD a c *
        shiftedTheta D c (-1 / τ) (τ⁻¹ • z) := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  let v (i : Fin D.rank) : ℂ := (z i).re
  let w (i : Fin D.rank) : ℂ := (z i).im
  let l (t : ℂ) := v + t • w
  let F (t : ℂ) := shiftedTheta D a τ (l t)
  let H (t : ℂ) :=
    ((Real.sqrt (gramReal D).det : ℂ)⁻¹ * (-Complex.I * τ) ^ (-(D.rank : ℂ) / 2)) *
    Complex.exp (-Real.pi * Complex.I / τ * sourceQuadratic (gramReal D) (l t)) *
    ∑ c : Discriminant D, pairingCharacter D hD a c *
      shiftedTheta D c (-1 / τ) (τ⁻¹ • l t)
  have ht0 : τ ≠ 0 := by intro h; simp [h] at hτ
  have htS : 0 < ((-1 : ℂ) / τ).im := by
    rw [div_im]
    simpa using div_neg_of_neg_of_pos (neg_neg_of_pos hτ) (Complex.normSq_pos.mpr ht0)
  have hF : Differentiable ℂ F := shiftedTheta_affine_entire D hD a τ hτ v w
  have hH : Differentiable ℂ H := by
    have hterms (c : Discriminant D) :
        Differentiable ℂ (fun t => shiftedTheta D c (-1 / τ) (τ⁻¹ • l t)) := by
      have hline (t : ℂ) : τ⁻¹ • l t = τ⁻¹ • v + t • (τ⁻¹ • w) := by
        dsimp only [l]
        rw [smul_add, smul_comm τ⁻¹ t]
      simpa only [hline] using
        shiftedTheta_affine_entire D hD c (-1 / τ) htS (τ⁻¹ • v) (τ⁻¹ • w)
    have hq : Differentiable ℂ (fun t => sourceQuadratic (gramReal D) (l t)) := by
      simp only [sourceQuadratic, dotProduct, mulVec, l, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      fun_prop
    dsimp only [H]
    apply Differentiable.mul
    · fun_prop
    · apply Differentiable.fun_sum
      intro c _
      fun_prop
  have hEq (r : ℝ) : F (r : ℂ) = H (r : ℂ) := by
    have hl : l (r : ℂ) = fun i => (((z i).re + r * (z i).im : ℝ) : ℂ) := by
      ext i
      simp [l, v, w]
    simpa only [F, H, hl] using
      shiftedTheta_real_S D hD a τ hτ (fun i => (z i).re + r * (z i).im)
  have ht : Tendsto ((↑) : ℝ → ℂ) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [ofReal_zero] using
        (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_compl_singleton_iff.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))
  have he : ∃ᶠ t in 𝓝[≠] (0 : ℂ), F t = H t := ht.frequently (Filter.Eventually.of_forall hEq).frequently
  have hid := (hF.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
    (hH.differentiableOn.analyticOnNhd isOpen_univ) he
  have hI : l Complex.I = z := by
    ext i
    simp [l, v, w, mul_comm Complex.I, Complex.re_add_im]
  simpa only [F, H, hI] using congrFun hid Complex.I

end D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta
