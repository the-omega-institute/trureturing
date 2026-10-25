import D5.S3.Geometry.Hyperideal.CFMPActualTriangleNormal435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicPlaneRealization
open CFMPReflectedCoefficientSection435Transient
open CFMPActualTriangleNormal435Transient

namespace CFMPActualPlaneBranch435Transient

-- The original reflection_future and vertical declarations need visibility
-- in the temporary owner copies. No proof of either is duplicated here.
theorem time_pos_of_den (X : Coeff) (hX : lorentz X X < 0)
    (hd : 0 < X 3 - X 2) : 0 < X 3 := by
  have hp : 0 < (X 3 - X 2) * (X 3 + X 2) := by
    simp [lorentz, Fin.sum_univ_four] at hX
    nlinarith [sq_nonneg (X 0), sq_nonneg (X 1)]
  have hsum := pos_of_mul_pos_right hp hd.le
  linarith

theorem den_pos_of_time (X : Coeff) (hX : lorentz X X < 0)
    (ht : 0 < X 3) : 0 < X 3 - X 2 := by
  have hs : 0 < Real.sqrt (-lorentz X X) := Real.sqrt_pos.mpr (neg_pos.mpr hX)
  have hunit := normalized_unit X hX
  have htime : 0 < ((Real.sqrt (-lorentz X X))⁻¹ • X) 3 :=
    mul_pos (inv_pos.mpr hs) ht
  have h := future_den _ hunit htime
  change 0 < (Real.sqrt (-lorentz X X))⁻¹ * X 3 -
    (Real.sqrt (-lorentz X X))⁻¹ * X 2 at h
  rw [← mul_sub] at h
  exact pos_of_mul_pos_right h (inv_pos.mpr hs).le

theorem reflection_future_timelike (A X : Coeff) (hA : 0 < lorentz A A)
    (hX : lorentz X X < 0) (ht : 0 < X 3) :
    0 < reflectionLinear A X 3 := by
  have hs : 0 < Real.sqrt (-lorentz X X) := Real.sqrt_pos.mpr (neg_pos.mpr hX)
  have htime : 0 < ((Real.sqrt (-lorentz X X))⁻¹ • X) 3 :=
    mul_pos (inv_pos.mpr hs) ht
  have h : 0 < reflectionLinear A ((Real.sqrt (-lorentz X X))⁻¹ • X) 3 := by
    rw [reflectionLinear_apply]
    exact reflection_future A _ hA (normalized_unit X hX) htime
  rw [map_smul] at h
  change 0 < (Real.sqrt (-lorentz X X))⁻¹ * reflectionLinear A X 3 at h
  exact pos_of_mul_pos_right h (inv_pos.mpr hs).le

theorem reflection_den_pos (A X : Coeff) (hA : 0 < lorentz A A)
    (hX : lorentz X X < 0) (hd : 0 < X 3 - X 2) :
    0 < reflectionLinear A X 3 - reflectionLinear A X 2 := by
  have hr : lorentz (reflectionLinear A X) (reflectionLinear A X) < 0 := by
    simpa only [reflectionLinear_apply, reflection_pair A X X hA.ne'] using hX
  exact den_pos_of_time _ hr
    (reflection_future_timelike A X hA hX (time_pos_of_den X hX hd))

-- This calculation uses the actual native vertical inclusion and original
-- native lift, rather than a replacement metric on coordinate triples.
theorem vertical_chart_lift (Y : Coeff) (hY : lorentz Y Y < 0)
    (ht : 0 < Y 3) (hy : Y 1 = 0) :
    ∃ z : UpperHalfPlane,
      z.re = Y 0 / (Y 3 - Y 2) ∧
      z.im = Real.sqrt (-lorentz Y Y) / (Y 3 - Y 2) ∧
      lift (vertical z) = (Real.sqrt (-lorentz Y Y))⁻¹ • Y := by
  have hs : 0 < Real.sqrt (-lorentz Y Y) := Real.sqrt_pos.mpr (neg_pos.mpr hY)
  have hd := den_pos_of_time Y hY ht
  let z : UpperHalfPlane :=
    ⟨Complex.mk (Y 0 / (Y 3 - Y 2))
      (Real.sqrt (-lorentz Y Y) / (Y 3 - Y 2)), div_pos hs hd⟩
  refine ⟨z, rfl, rfl, ?_⟩
  apply lift_of_coordinates _ _ (normalized_unit Y hY)
    (show 0 < ((Real.sqrt (-lorentz Y Y))⁻¹ • Y) 3 from
      mul_pos (inv_pos.mpr hs) ht)
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply Complex.ext <;>
      simp [vertical, z, Pi.smul_apply, smul_eq_mul, UpperHalfPlane.re,
        UpperHalfPlane.im, hy] <;>
      field_simp [hs.ne', hd.ne']
    <;> ring
  · simp [vertical, z, Pi.smul_apply, smul_eq_mul, UpperHalfPlane.re,
      UpperHalfPlane.im]
    field_simp [hs.ne', hd.ne']
    <;> ring

-- The same reflected chart point returns to the original normalized point.
-- The denominator after reflection is allowed to differ from the original one.
theorem actual_reflected_chart_lift (A X : Coeff) (hA : 0 < lorentz A A)
    (hX : lorentz X X < 0) (hd : 0 < X 3 - X 2)
    (hplane : reflectionLinear A X 1 = 0) :
    ∃ z : UpperHalfPlane,
      z.re = reflectionLinear A X 0 /
        (reflectionLinear A X 3 - reflectionLinear A X 2) ∧
      z.im = Real.sqrt (-lorentz X X) /
        (reflectionLinear A X 3 - reflectionLinear A X 2) ∧
      reflectionLinear A (lift (vertical z)) =
        (Real.sqrt (-lorentz X X))⁻¹ • X := by
  have hpair : lorentz (reflectionLinear A X) (reflectionLinear A X) =
      lorentz X X := by
    simpa only [reflectionLinear_apply] using reflection_pair A X X hA.ne'
  obtain ⟨z, hzre, hzim, hzl⟩ := vertical_chart_lift (reflectionLinear A X)
    (by rw [hpair]; exact hX)
    (reflection_future_timelike A X hA hX (time_pos_of_den X hX hd)) hplane
  refine ⟨z, hzre, ?_, ?_⟩
  · simpa only [hpair] using hzim
  · rw [hzl, map_smul, hpair]
    congr 1
    simpa only [reflectionLinear_apply] using reflection_involutive A hA.ne' X

end CFMPActualPlaneBranch435Transient
