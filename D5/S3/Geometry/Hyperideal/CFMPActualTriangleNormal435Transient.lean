import D5.S3.Geometry.Hyperideal.CFMPReflectedCoefficientSection435Transient
import D5.S3.Geometry.HyperbolicPlaneRealization
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicPlaneRealization
open CFMPReflectedCoefficientSection435Transient

namespace CFMPActualTriangleNormal435Transient

-- Compilation needs the original null-orthogonality lemma exposed in its owner.
-- This file is temporary application evidence, not proposed frozen declarations.
theorem normalized_unit (T : Coeff) (hT : lorentz T T < 0) :
    lorentz ((Real.sqrt (-lorentz T T))⁻¹ • T)
      ((Real.sqrt (-lorentz T T))⁻¹ • T) = -1 := by
  have hr : 0 < -lorentz T T := neg_pos.mpr hT
  have hs : Real.sqrt (-lorentz T T) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have he : lorentz ((Real.sqrt (-lorentz T T))⁻¹ • T)
        ((Real.sqrt (-lorentz T T))⁻¹ • T) =
      (Real.sqrt (-lorentz T T))⁻¹ ^ 2 * lorentz T T := by
    simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [he]
  have hsq := Real.sq_sqrt hr.le
  field_simp [hs]
  nlinarith [hsq]

theorem spacelike_of_timelike_orthogonal (T N : Coeff)
    (hT : lorentz T T < 0) (horth : lorentz T N = 0) (hN : N ≠ 0) :
    0 < lorentz N N := by
  have ht : 0 < (T 3)^2 := by
    simp [lorentz, Fin.sum_univ_four] at hT
    nlinarith [sq_nonneg (T 0), sq_nonneg (T 1), sq_nonneg (T 2)]
  let W : Coeff := T 3 • N - N 3 • T
  have hwtime : W 3 = 0 := by simp [W, smul_eq_mul]; ring
  have hw : 0 ≤ lorentz W W := by
    simp [lorentz, Fin.sum_univ_four, hwtime]
    nlinarith [sq_nonneg (W 0), sq_nonneg (W 1), sq_nonneg (W 2)]
  have hid : (T 3)^2 * lorentz N N =
      lorentz W W + (-lorentz T T) * (N 3)^2 := by
    simp [W, lorentz, Fin.sum_univ_four, smul_eq_mul] at horth ⊢
    linear_combination (2 * T 3 * N 3) * horth
  have hnonneg : 0 ≤ lorentz N N := by
    have hright : 0 ≤ lorentz W W + (-lorentz T T) * (N 3)^2 :=
      add_nonneg hw (mul_nonneg (neg_pos.mpr hT).le (sq_nonneg _))
    rw [← hid] at hright
    exact nonneg_of_mul_nonneg_right hright ht
  apply lt_of_le_of_ne hnonneg
  intro hz
  apply hN
  apply lorentz_null_orthogonal
      ((Real.sqrt (-lorentz T T))⁻¹ • T) N (normalized_unit T hT) hz.symm
  have he : lorentz ((Real.sqrt (-lorentz T T))⁻¹ • T) N =
      (Real.sqrt (-lorentz T T))⁻¹ * lorentz T N := by
    simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [he, horth, mul_zero]

-- The witness belongs to the same coefficient plane, even when the affine
-- origin is outside the parameter set.
theorem exists_actual_spacelike_normal (M : M4) (a b c : Coeff)
    (p : Fin 2 → ℝ)
    (ht : lorentz ((a + p 0 • b + p 1 • c) ᵥ* M)
      ((a + p 0 • b + p 1 • c) ᵥ* M) < 0) :
    ∃ N : Coeff, 0 < lorentz N N ∧
      lorentz (a ᵥ* M) N = 0 ∧ lorentz (b ᵥ* M) N = 0 ∧
      lorentz (c ᵥ* M) N = 0 ∧
      ∀ q : Fin 2 → ℝ, lorentz ((a + q 0 • b + q 1 • c) ᵥ* M) N = 0 := by
  obtain ⟨N, hN, ha, hb, hc⟩ :=
    exists_triangle_normal (a ᵥ* M) (b ᵥ* M) (c ᵥ* M)
  have hplane (q : Fin 2 → ℝ) :
      lorentz ((a + q 0 • b + q 1 • c) ᵥ* M) N = 0 := by
    have he : lorentz ((a + q 0 • b + q 1 • c) ᵥ* M) N =
        lorentz (a ᵥ* M) N + q 0 * lorentz (b ᵥ* M) N +
          q 1 * lorentz (c ᵥ* M) N := by
      simp [Matrix.add_vecMul, Matrix.smul_vecMul, lorentz,
        Fin.sum_univ_four, smul_eq_mul]
      ring
    rw [he, ha, hb, hc]
    ring
  exact ⟨N, spacelike_of_timelike_orthogonal _ N ht (hplane p) hN,
    ha, hb, hc, hplane⟩

theorem exists_actual_spacelike_normal_on_nonempty (M : M4) (a b c : Coeff)
    (K : Set (Fin 2 → ℝ)) (hK : K.Nonempty)
    (hr : ∀ p ∈ K, 0 < -lorentz ((a + p 0 • b + p 1 • c) ᵥ* M)
      ((a + p 0 • b + p 1 • c) ᵥ* M)) :
    ∃ N : Coeff, 0 < lorentz N N ∧
      lorentz (a ᵥ* M) N = 0 ∧ lorentz (b ᵥ* M) N = 0 ∧
      lorentz (c ᵥ* M) N = 0 ∧
      ∀ q : Fin 2 → ℝ, lorentz ((a + q 0 • b + q 1 • c) ᵥ* M) N = 0 := by
  obtain ⟨p, hp⟩ := hK
  exact exists_actual_spacelike_normal M a b c p (neg_pos.mp (hr p hp))

-- This is the original reflection, with its linearity bundled for the
-- already prepared inverse-section and tangent-rank application.
def reflectionLinear (A : Coeff) : Coeff →ₗ[ℝ] Coeff :=
  LinearMap.id - (2 / lorentz A A) • (pairing A).smulRight A

theorem reflectionLinear_apply (A X : Coeff) :
    reflectionLinear A X = reflectPlane A X := by
  ext i
  simp [reflectionLinear, reflectPlane, pairing_apply, lorentz_symm,
    smul_eq_mul, div_eq_mul_inv]
  ring

theorem reflection_coordinate_zero (A N : Coeff) (s : ℝ)
    (hA : lorentz A A ≠ 0) (hs : s ≠ 0)
    (hadapt : ∀ X, lorentz (reflectPlane A X) N = -s * X 1)
    (X : Coeff) (hX : lorentz X N = 0) : reflectionLinear A X 1 = 0 := by
  have h := hadapt (reflectPlane A X)
  rw [reflection_involutive A hA X, hX] at h
  rw [reflectionLinear_apply]
  exact (mul_eq_zero.mp h.symm).resolve_left (neg_ne_zero.mpr hs)

-- Every point of the original coefficient plane uses this one reflection.
-- No original boundary-support normal is substituted for an internal face.
theorem exists_actual_reflected_section (M : M4) (hM : M.det ≠ 0)
    (a b c : Coeff) (p : Fin 2 → ℝ)
    (ht : lorentz ((a + p 0 • b + p 1 • c) ᵥ* M)
      ((a + p 0 • b + p 1 • c) ᵥ* M) < 0)
    (hsa : ∑ i, a i = 1) (hsb : ∑ i, b i = 0) (hsc : ∑ i, c i = 0)
    (hbc : Function.Injective (fun q : Fin 2 → ℝ => q 0 • b + q 1 • c)) :
    ∃ R : Coeff →ₗ[ℝ] Coeff, Function.Involutive R ∧
      (∀ X Y, lorentz (R X) (R Y) = lorentz X Y) ∧
      R (a ᵥ* M) 1 = 0 ∧ R (b ᵥ* M) 1 = 0 ∧ R (c ᵥ* M) 1 = 0 ∧
      sectionMap M R (forward M R a) = 1 ∧
      (∀ j, sectionMap M R ((reflectedTangents M R b c).col j) = 0) ∧
      (CFMPReflectedPlaneChart435Transient.augmented
        (reflectedTangents M R b c) (forward M R a)).det ≠ 0 := by
  obtain ⟨N, hN, ha, hb, hc, _⟩ := exists_actual_spacelike_normal M a b c p ht
  obtain ⟨A, s, hA, hs, hadapt⟩ := adapted_reflection N hN
  let R := reflectionLinear A
  have hR : Function.Involutive R := by
    intro X
    simpa only [R, reflectionLinear_apply] using reflection_involutive A hA.ne' X
  have hpair (X Y : Coeff) : lorentz (R X) (R Y) = lorentz X Y := by
    simpa only [R, reflectionLinear_apply] using reflection_pair A X Y hA.ne'
  have hra : R (a ᵥ* M) 1 = 0 :=
    reflection_coordinate_zero A N s hA.ne' hs hadapt _ ha
  have hrb : R (b ᵥ* M) 1 = 0 :=
    reflection_coordinate_zero A N s hA.ne' hs hadapt _ hb
  have hrc : R (c ᵥ* M) 1 = 0 :=
    reflection_coordinate_zero A N s hA.ne' hs hadapt _ hc
  have hsection := actual_section_data M R hM hR a b c hra hrb hrc hsa hsb hsc
  exact ⟨R, hR, hpair, hra, hrb, hrc, hsection.1, hsection.2,
    actual_augmented_det_ne_zero M R hM hR a b c hra hrb hrc hsa hsb hsc hbc⟩

end CFMPActualTriangleNormal435Transient

#print axioms CFMPActualTriangleNormal435Transient.exists_actual_reflected_section
run_cmd do
  let name := ``CFMPActualTriangleNormal435Transient.exists_actual_reflected_section
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP223 original section absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP223 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP223 CHECKED CFMPActualTriangleNormal435Transient.exists_actual_reflected_section axioms={axioms}"
