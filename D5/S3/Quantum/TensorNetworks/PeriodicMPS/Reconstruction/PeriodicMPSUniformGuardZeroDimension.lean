/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The exact native guard-zero locus has real Hausdorff dimension at most six. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralCoefficients
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformPhysicalAlgebraicGuard

/-! The real zero locus of the spectral-localization guard in the ordinary coordinates of the uniform periodic matrix product state. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformGuardZeroDimension

open Set MvPolynomial
open PeriodicMPSUniformSpecialDivisorExclusion
  (Variable AmbientPolynomials ambientU ambientGuard ambientGuard_formula
    spectralCoefficients nativeSliceSubstitution)
open PeriodicMPSUniformCompactGraph (Parameters)
open PeriodicMPSUniformPhysicalAlgebraicGuard
  (physicalGuard dimH_physicalGuard_zero_le dimH_zeroMixed_parameters_le)
open SevenSiteCriticalCertificate (sliceBlock)
open SevenSitePhysicalRankBridge (SlicePoint align)
open SevenSitePhysicalRankAssembly (alignedSlice asOrdinary)

open private nativeCartesian from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralCoefficients

noncomputable section

abbrev NativePolynomials := MvPolynomial (Fin 5) ℂ

/-- The determinant pencil uses the ket coordinates d, e and their independent bra
coordinates db, eb, with a single aligned mixed-trace coordinate k. -/
def determinantVariables : Variable → NativePolynomials
  | none => X 1
  | some .d => sliceBlock (C Complex.I) X true 0
  | some .db => sliceBlock (C Complex.I) X false 0
  | some .e => sliceBlock (C Complex.I) X true 2
  | some .eb => sliceBlock (C Complex.I) X false 2

/-- Pull determinant-pencil polynomials back to the native Cartesian slice. -/
def pullback : AmbientPolynomials →+* NativePolynomials :=
  eval₂Hom C determinantVariables

/-- The polynomial inverted by the spectral localization, in native coordinates. -/
def nativeGuard : NativePolynomials := pullback ambientGuard

/-- The polynomial used by the SevenSite physical cover is exactly the
pullback of the spectral localization guard. -/
theorem nativeGuard_eq_physicalGuard : nativeGuard = physicalGuard := by
  rw [nativeGuard, ambientGuard_formula]
  simp [pullback, ambientU, PeriodicMPSUniformSpecialDivisorExclusion.ambientK,
    spectralCoefficients, determinantVariables, physicalGuard, sliceBlock]
  ring_nf
  simp

private def evaluateSlice (x : SlicePoint) : NativePolynomials →+* ℂ :=
  eval (fun i => (x i : ℂ))

/-- The two determinant factors on the real slice, with the literal sign of
the mixed determinant term. -/
theorem eval_guard_factors (x : SlicePoint) :
    eval (fun i => (x i : ℂ)) (pullback ambientU) =
      ((x 0 ^ 2 + x 3 ^ 2 : ℝ) : ℂ) ∧
    spectralCoefficients (fun j => eval (fun i => (x i : ℂ)) (determinantVariables j)) 2 -
      spectralCoefficients (fun j => eval (fun i => (x i : ℂ)) (determinantVariables j)) 1 ^ 2 =
      ((x 1 ^ 2 * ((x 0 + x 2) ^ 2 + (x 3 - x 4) ^ 2) : ℝ) : ℂ) := by
  change evaluateSlice x (pullback ambientU) = _ ∧
    spectralCoefficients (evaluateSlice x ∘ determinantVariables) 2 -
      spectralCoefficients (evaluateSlice x ∘ determinantVariables) 1 ^ 2 = _
  constructor
  · apply Complex.ext <;>
      simp [evaluateSlice, pullback, ambientU, determinantVariables, sliceBlock,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, pow_two]
    ring
  · apply Complex.ext <;>
      simp [spectralCoefficients, evaluateSlice, determinantVariables, sliceBlock,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, pow_two] <;> ring

/-- Both three-coordinate linear slice images and both stereographic phase
frames from the physical chart give the ambient bound on this sector. -/
theorem dimH_nativeGuard_zero_of_mixedTrace_ne_zero :
    dimH {u : Parameters | (align (asOrdinary u)).2.2.2 ≠ 0 ∧
      eval (fun i => (alignedSlice (asOrdinary u) i : ℂ)) nativeGuard = 0} ≤ 6 := by
  simpa only [nativeGuard_eq_physicalGuard] using dimH_physicalGuard_zero_le

/-- The two linear slices of the exact guard when the aligned mixed trace is positive. -/
theorem eval_nativeGuard_eq_zero_iff (x : SlicePoint) (hk : 0 < x 1) :
    eval (fun i => (x i : ℂ)) nativeGuard = 0 ↔
      (x 0 = 0 ∧ x 3 = 0) ∨ (x 0 = -x 2 ∧ x 3 = x 4) := by
  rw [nativeGuard_eq_physicalGuard]
  exact PeriodicMPSUniformPhysicalAlgebraicGuard.eval_physicalGuard_eq_zero_iff x hk

/-- This bound also holds in the full ambient space of ordinary parameters. -/
theorem dimH_nativeGuard_zero :
    dimH {u : Parameters |
      eval (fun i => (alignedSlice (asOrdinary u) i : ℂ)) nativeGuard = 0} ≤ 6 := by
  have hsubset :
      {u : Parameters | eval (fun i => (alignedSlice (asOrdinary u) i : ℂ)) nativeGuard = 0} ⊆
        {u : Parameters | (align (asOrdinary u)).2.2.2 = 0} ∪
        {u : Parameters | (align (asOrdinary u)).2.2.2 ≠ 0 ∧
          eval (fun i => (alignedSlice (asOrdinary u) i : ℂ)) nativeGuard = 0} := by
    intro u hu
    by_cases h : (align (asOrdinary u)).2.2.2 = 0
    · exact Or.inl h
    · exact Or.inr ⟨h, hu⟩
  refine (dimH_mono hsubset).trans ?_
  rw [dimH_union]
  exact sup_le dimH_zeroMixed_parameters_le dimH_nativeGuard_zero_of_mixedTrace_ne_zero

private theorem half_times_two {σ : Type*} :
    C (1 / 2 : ℂ) * (2 : MvPolynomial σ ℂ) = 1 := by
  rw [← map_ofNat C, ← map_mul]
  norm_num

private theorem inv_twoI_times_twoI {σ : Type*} :
    C ((2 * Complex.I)⁻¹) * (2 * C Complex.I : MvPolynomial σ ℂ) = 1 := by
  rw [← map_ofNat C, ← map_mul, ← map_mul, inv_mul_cancel₀]
  · exact map_one C
  · exact mul_ne_zero (by norm_num) Complex.I_ne_zero

private theorem pullback_nativeSliceSubstitution :
    pullback.comp nativeSliceSubstitution = RingHom.id NativePolynomials := by
  apply MvPolynomial.ringHom_ext
  · simp [pullback, nativeSliceSubstitution]
  · intro i
    simp only [RingHom.comp_apply, nativeSliceSubstitution, eval₂Hom_X', RingHom.id_apply]
    have hX (j : Variable) : pullback (X j) = determinantVariables j :=
      eval₂Hom_X' _ _ _
    have hC (a : ℂ) : pullback (C a) = C a := eval₂Hom_C _ _ _
    have hd : determinantVariables (some .d) = X 0 + C Complex.I * X 3 := rfl
    have hdb : determinantVariables (some .db) = X 0 + (-C Complex.I) * X 3 := rfl
    have he : determinantVariables (some .e) = X 2 + C Complex.I * X 4 := rfl
    have heb : determinantVariables (some .eb) = X 2 + (-C Complex.I) * X 4 := rfl
    fin_cases i <;> simp only [nativeCartesian, Matrix.cons_val_succ', Matrix.cons_val_zero']
    · rw [map_mul, map_add, hC, hX, hX, hd, hdb]
      change _ = X (0 : Fin 5)
      linear_combination X 0 * half_times_two
    · exact hX none
    · rw [map_mul, map_add, hC, hX, hX, he, heb]
      change _ = X (2 : Fin 5)
      linear_combination X 2 * half_times_two
    · rw [map_mul, map_sub, hC, hX, hX, hd, hdb]
      change _ = X (3 : Fin 5)
      linear_combination X 3 * inv_twoI_times_twoI
    · rw [map_mul, map_sub, hC, hX, hX, he, heb]
      change _ = X (4 : Fin 5)
      linear_combination X 4 * inv_twoI_times_twoI

private theorem imagCoefficient {σ : Type*} :
    (C Complex.I : MvPolynomial σ ℂ) * C ((2 * Complex.I)⁻¹) = C (1 / 2) := by
  rw [← map_mul]
  congr 1
  field_simp [Complex.I_ne_zero]

private theorem nativeSliceSubstitution_pullback :
    nativeSliceSubstitution.comp pullback = RingHom.id AmbientPolynomials := by
  apply MvPolynomial.ringHom_ext
  · simp [pullback, nativeSliceSubstitution]
  · intro j
    simp only [RingHom.comp_apply, pullback, eval₂Hom_X', RingHom.id_apply]
    have hX (i : Fin 5) : nativeSliceSubstitution (X i) = nativeCartesian X i :=
      eval₂Hom_X' _ _ _
    have hC (a : ℂ) : nativeSliceSubstitution (C a) = C a := eval₂Hom_C _ _ _
    have hplus (a b : AmbientPolynomials) :
        C (1 / 2) * (a + b) + C Complex.I * (C ((2 * Complex.I)⁻¹) * (a - b)) = a := by
      rw [← mul_assoc (C Complex.I), imagCoefficient]
      linear_combination a * half_times_two
    have hminus (a b : AmbientPolynomials) :
        C (1 / 2) * (a + b) + (-C Complex.I) * (C ((2 * Complex.I)⁻¹) * (a - b)) = b := by
      rw [neg_mul, ← mul_assoc (C Complex.I), imagCoefficient]
      linear_combination b * half_times_two
    rcases j with _ | j
    · exact hX 1
    cases j
    · change nativeSliceSubstitution (X 0 + C Complex.I * X 3) = _
      rw [map_add, map_mul, hC, hX, hX]
      exact hplus _ _
    · change nativeSliceSubstitution (X 0 + (-C Complex.I) * X 3) = _
      rw [map_add, map_mul, map_neg, hC, hX, hX]
      exact hminus _ _
    · change nativeSliceSubstitution (X 2 + C Complex.I * X 4) = _
      rw [map_add, map_mul, hC, hX, hX]
      exact hplus _ _
    · change nativeSliceSubstitution (X 2 + (-C Complex.I) * X 4) = _
      rw [map_add, map_mul, map_neg, hC, hX, hX]
      exact hminus _ _

/-- The literal Cartesian substitution from the spectral proof is a change of
coordinates over the complex polynomial ring. -/
def nativeSliceEquiv : NativePolynomials ≃+* AmbientPolynomials :=
  RingEquiv.ofRingHom nativeSliceSubstitution pullback nativeSliceSubstitution_pullback
    pullback_nativeSliceSubstitution

@[simp] theorem nativeSliceEquiv_apply (p : NativePolynomials) :
    nativeSliceEquiv p = nativeSliceSubstitution p := rfl

@[simp] theorem nativeSliceEquiv_nativeGuard : nativeSliceEquiv nativeGuard = ambientGuard :=
  nativeSliceEquiv.apply_symm_apply ambientGuard

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformGuardZeroDimension
