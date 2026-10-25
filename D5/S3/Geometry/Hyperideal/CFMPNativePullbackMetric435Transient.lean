import D5.S3.Geometry.Hyperideal.CFMPLorentzLiftSurface435Transient
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
open scoped Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open CFMPLorentzLiftSurface435Transient

namespace CFMPNativePullbackMetric435Transient

def radius (U : W) : ℝ := -lorentz U U

def delta (U : W) : ℝ := U 3 - U 2

def nativeMap (U : W) : V :=
  ![U 0 / delta U, U 1 / delta U, Real.sqrt (radius U) / delta U]

def nativeMatrix (U : W) : Matrix (Fin 3) (Fin 4) ℝ :=
  let s := Real.sqrt (radius U)
  let d := delta U
  !![1/d, 0, U 0/d^2, -U 0/d^2;
     0, 1/d, U 1/d^2, -U 1/d^2;
     -U 0/(s*d), -U 1/(s*d), -U 2/(s*d)+s/d^2, U 3/(s*d)-s/d^2]

theorem nativeMap_hasFDerivAt (U : W) (hU : 0 < radius U) (hd : delta U ≠ 0) :
    HasFDerivAt nativeMap (nativeMatrix U).mulVecLin.toContinuousLinearMap U := by
  have h (i : Fin 4) : HasFDerivAt (fun X : W => X i)
      (ContinuousLinearMap.proj i) U := (ContinuousLinearMap.proj i : W →L[ℝ] ℝ).hasFDerivAt
  have hQ := (((h 0).mul (h 0)).add ((h 1).mul (h 1)) |>.add ((h 2).mul (h 2))).sub ((h 3).mul (h 3)) |>.neg
  have hRadius : (fun X : W => -((X 0*X 0+X 1*X 1+X 2*X 2)-X 3*X 3)) = radius := by
    funext X
    simp [radius, lorentz, Fin.sum_univ_four]
    <;> ring
  change HasFDerivAt (fun X : W => -((X 0*X 0+X 1*X 1+X 2*X 2)-X 3*X 3)) _ U at hQ
  rw [hRadius] at hQ
  have hD := (h 3).sub (h 2)
  have hInv := (hasDerivAt_inv hd).comp_hasFDerivAt U hD
  have hS := hQ.sqrt hU.ne'
  have hs : Real.sqrt (radius U) ≠ 0 := (Real.sqrt_pos.mpr hU).ne'
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert (h 0).mul hInv using 1
    · funext X; simp [nativeMap, delta, div_eq_mul_inv]
    · ext v
      simp [nativeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, delta, smul_eq_mul]
      <;> field_simp [show U 3 - U 2 ≠ 0 from hd]
      <;> ring
  · convert (h 1).mul hInv using 1
    · funext X; simp [nativeMap, delta, div_eq_mul_inv]
    · ext v
      simp [nativeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, delta, smul_eq_mul]
      <;> field_simp [show U 3 - U 2 ≠ 0 from hd]
      <;> ring
  · convert hS.mul hInv using 1
    · funext X; simp [nativeMap, delta, div_eq_mul_inv]
    · ext v
      simp [nativeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, delta, smul_eq_mul]
      <;> field_simp [show U 3 - U 2 ≠ 0 from hd, hs]
      <;> ring

def normalizedTangent (U v : W) : W :=
  (Real.sqrt (radius U))⁻¹ • v +
    (lorentz U v / (Real.sqrt (radius U))^3) • U

theorem normalizedTangent_lorentz (U v w : W) (hU : 0 < radius U) :
    lorentz (normalizedTangent U v) (normalizedTangent U w) =
      lorentz v w / radius U + lorentz U v * lorentz U w / (radius U)^2 := by
  let s := Real.sqrt (radius U)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hU).ne'
  have hsq : s^2 = radius U := Real.sq_sqrt hU.le
  have hUU : lorentz U U = -s^2 := by rw [hsq]; simp only [radius, neg_neg]
  change lorentz (s⁻¹ • v + (lorentz U v / s^3) • U)
    (s⁻¹ • w + (lorentz U w / s^3) • U) = _
  rw [lorentz_linear, lorentz_symm v U, hUU, ← hsq]
  field_simp [hs]
  <;> ring

end CFMPNativePullbackMetric435Transient
