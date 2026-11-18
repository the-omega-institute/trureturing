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

end D5.S3.VertexAlgebra.LatticeDiscriminantShiftedTheta
