import D5.S3.Geometry.Hyperideal.CFMPActualPlaneBranch435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicPlaneRealization
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPReflectedCoefficientSection435Transient
open CFMPActualTriangleNormal435Transient
open CFMPActualPlaneBranch435Transient

namespace CFMPActualPlaneIsometry435Transient

def reflectionNative (A : Coeff) (hA : 0 < lorentz A A)
    (p : HyperbolicThreeSpace) : HyperbolicThreeSpace :=
  project (reflectionLinear A (lift p))
    (by simpa only [reflectionLinear_apply, reflection_pair A _ _ hA.ne']
      using lift_unit p)
    (by simpa only [reflectionLinear_apply] using
      reflection_future A (lift p) hA (lift_unit p) (lift_time p))

theorem reflectionNative_lift (A : Coeff) (hA : 0 < lorentz A A)
    (p : HyperbolicThreeSpace) :
    lift (reflectionNative A hA p) = reflectionLinear A (lift p) := by
  apply lift_of_coordinates
  · simpa only [reflectionLinear_apply, reflection_pair A _ _ hA.ne']
      using lift_unit p
  · simpa only [reflectionLinear_apply] using
      reflection_future A (lift p) hA (lift_unit p) (lift_time p)
  · rfl

theorem reflectionNative_isometry (A : Coeff) (hA : 0 < lorentz A A) :
    Isometry (reflectionNative A hA) := by
  apply Isometry.of_dist_eq
  intro p q
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  have h := reflection_pair A (lift p) (lift q) hA.ne'
  simp only [← reflectionLinear_apply, ← reflectionNative_lift A hA] at h
  rw [lift_cosh, lift_cosh] at h
  exact neg_injective h

theorem vertical_isometry : Isometry vertical := by
  apply Isometry.of_dist_eq
  intro z w
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  have h := vertical_cosh z w
  rw [lift_cosh] at h
  exact neg_injective h

theorem same_original_point (A X : Coeff) (hA : 0 < lorentz A A)
    (hX : lorentz X X < 0) (hd : 0 < X 3 - X 2)
    (hplane : reflectionLinear A X 1 = 0)
    (p : HyperbolicThreeSpace)
    (hp : lift p = (Real.sqrt (-lorentz X X))⁻¹ • X) :
    ∃ z : UpperHalfPlane,
      z.re = reflectionLinear A X 0 /
        (reflectionLinear A X 3 - reflectionLinear A X 2) ∧
      z.im = Real.sqrt (-lorentz X X) /
        (reflectionLinear A X 3 - reflectionLinear A X 2) ∧
      reflectionNative A hA (vertical z) = p := by
  obtain ⟨z,hzr,hzi,hz⟩ := actual_reflected_chart_lift A X hA hX hd hplane
  refine ⟨z,hzr,hzi,?_⟩
  apply lift_injective
  rw [reflectionNative_lift, hz, hp]

-- This is the same finite Gram pullback calculation from shared_radial_body.
theorem frame_quadratic (l : Fin 6 → ℝ) (M : M4)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (v : Coeff) :
    lorentz (v ᵥ* M) (v ᵥ* M) = gramQuadratic l v := by
  calc
    _ = ∑ k, ∑ i, ∑ j, v i * v j *
        ((![(1 : ℝ),1,1,-1] k) * M i k * M j k) := by
      simp only [lorentz, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ k, v i * v j *
        ((![(1 : ℝ),1,1,-1] k) * M i k * M j k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, v i * v j * lengthGram l i j := by
      simp_rw [← Finset.mul_sum]
      change (∑ i, ∑ j, v i * v j * lorentz (M i) (M j)) = _
      simp only [hG]
    _ = _ := by
      unfold gramQuadratic
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem original_frame_normalized_lift (l : Fin 6 → ℝ) (M : M4)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (v : cutBody l) :
    lift (f v) = (Real.sqrt (-lorentz (v.val ᵥ* M) (v.val ᵥ* M)))⁻¹ •
      (v.val ᵥ* M) := by
  obtain ⟨y,hy,hu,ht,hc⟩ := hf v
  have hlift := (lift_of_coordinates _ _ hu ht hc).trans hy
  have hr : radial l v.val = (Real.sqrt (-gramQuadratic l v.val))⁻¹ • v.val := by
    ext i
    simp [radial, div_eq_mul_inv, smul_eq_mul, mul_comm]
  rw [hlift, frame_quadratic l M hG, hr, Matrix.smul_vecMul]

-- One reflected vector A is retained throughout section, determinant and metric.
theorem same_A_section_and_isometry (M : M4) (hM : M.det ≠ 0)
    (a b c : Coeff) (p : Fin 2 → ℝ)
    (ht : lorentz ((a + p 0 • b + p 1 • c) ᵥ* M)
      ((a + p 0 • b + p 1 • c) ᵥ* M) < 0)
    (hsa : ∑ i, a i = 1) (hsb : ∑ i, b i = 0) (hsc : ∑ i, c i = 0)
    (hbc : Function.Injective (fun q : Fin 2 → ℝ => q 0 • b + q 1 • c)) :
    ∃ A : Coeff, ∃ hA : 0 < lorentz A A,
      Isometry (fun z => reflectionNative A hA (vertical z)) ∧
      (∀ q : Fin 2 → ℝ,
        reflectionLinear A ((a + q 0 • b + q 1 • c) ᵥ* M) 1 = 0) ∧
      sectionMap M (reflectionLinear A) (forward M (reflectionLinear A) a) = 1 ∧
      (∀ j, sectionMap M (reflectionLinear A)
        ((reflectedTangents M (reflectionLinear A) b c).col j) = 0) ∧
      (CFMPReflectedPlaneChart435Transient.augmented
        (reflectedTangents M (reflectionLinear A) b c)
        (forward M (reflectionLinear A) a)).det ≠ 0 := by
  obtain ⟨N,hN,ha,hb,hc,hall⟩ := exists_actual_spacelike_normal M a b c p ht
  obtain ⟨A,s,hA,hs,hadapt⟩ := adapted_reflection N hN
  have hR : Function.Involutive (reflectionLinear A) := by
    intro X
    simpa only [reflectionLinear_apply] using reflection_involutive A hA.ne' X
  have hra := reflection_coordinate_zero A N s hA.ne' hs hadapt _ ha
  have hrb := reflection_coordinate_zero A N s hA.ne' hs hadapt _ hb
  have hrc := reflection_coordinate_zero A N s hA.ne' hs hadapt _ hc
  have hsection := actual_section_data M (reflectionLinear A) hM hR a b c
    hra hrb hrc hsa hsb hsc
  refine ⟨A,hA,(reflectionNative_isometry A hA).comp vertical_isometry,?_,
    hsection.1,hsection.2,?_⟩
  · intro q
    exact reflection_coordinate_zero A N s hA.ne' hs hadapt _ (hall q)
  · exact actual_augmented_det_ne_zero M (reflectionLinear A) hM hR a b c
      hra hrb hrc hsa hsb hsc hbc

end CFMPActualPlaneIsometry435Transient
