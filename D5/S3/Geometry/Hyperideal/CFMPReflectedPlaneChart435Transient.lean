import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators

namespace CFMPReflectedPlaneChart435Transient

abbrev E := Fin 2 → ℝ
abbrev W := Fin 3 → ℝ
abbrev A32 := Matrix (Fin 3) (Fin 2) ℝ

-- Coordinates are the reflected Lorentz coordinates (v₀,v₂,v₃).
def radius (v : W) : ℝ := (v 2)^2 - (v 1)^2 - (v 0)^2
def delta (v : W) : ℝ := v 2 - v 1
def chart (v : W) : E := ![v 0 / delta v, Real.sqrt (radius v) / delta v]
def deltaRow (a : A32) (j : Fin 2) : ℝ := a 2 j - a 1 j
def radialRow (a : A32) (v : W) (j : Fin 2) : ℝ :=
  v 2 * a 2 j - v 1 * a 1 j - v 0 * a 0 j
def jacobian (a : A32) (v : W) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then
    (delta v * a 0 j - v 0 * deltaRow a j) / (delta v)^2
  else (delta v * radialRow a v j - radius v * deltaRow a j) /
    (Real.sqrt (radius v) * (delta v)^2)

def augmented (a : A32) (v : W) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![v 0,v 1,v 2; a 0 0,a 1 0,a 2 0; a 0 1,a 1 1,a 2 1]

def rowMap (a : A32) (i : Fin 3) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp a.mulVecLin.toContinuousLinearMap
def radialMap (a : A32) (v : W) : E →L[ℝ] ℝ :=
  v 2 • rowMap a 2 - v 1 • rowMap a 1 - v 0 • rowMap a 0

-- The derivative is of the displayed coordinate function.
theorem chart_hasFDerivAt (f : E → W) (a : A32) (q : E)
    (hf : ∀ i, HasFDerivAt (fun w => f w i) (rowMap a i) q)
    (hr : 0 < radius (f q)) (hd : delta (f q) ≠ 0) :
    HasFDerivAt (fun w => chart (f w))
      (jacobian a (f q)).mulVecLin.toContinuousLinearMap q := by
  have hdelta : HasFDerivAt (fun w => delta (f w))
      (rowMap a 2 - rowMap a 1) q := (hf 2).sub (hf 1)
  have hinv := (hasDerivAt_inv hd).comp_hasFDerivAt q hdelta
  have hrad : HasFDerivAt (fun w => radius (f w))
      (2 • radialMap a (f q)) q := by
    have h := (((hf 2).mul (hf 2)).sub ((hf 1).mul (hf 1))).sub
      ((hf 0).mul (hf 0))
    convert h using 1
    · funext w
      simp [radius, pow_two]
    · ext w
      simp [radialMap, smul_eq_mul]
      <;> ring
  have hroot := hrad.sqrt hr.ne'
  have hs : Real.sqrt (radius (f q)) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hsq := Real.sq_sqrt hr.le
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert (hf 0).mul hinv using 1
    · funext w
      simp [chart, div_eq_mul_inv]
    · ext w
      simp [jacobian, rowMap, deltaRow, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, smul_eq_mul]
      <;> field_simp [hd]
      <;> ring
  · convert hroot.mul hinv using 1
    · funext w
      simp [chart, div_eq_mul_inv]
    · ext w
      simp [jacobian, rowMap, radialMap, radialRow, deltaRow,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
      <;> field_simp [hd, hs]
      <;> ring_nf
      <;> simp only [hsq]
      <;> ring

theorem jacobian_det (a : A32) (v : W)
    (hr : 0 < radius v) (hd : delta v ≠ 0) :
    (jacobian a v).det = (augmented a v).det /
      (Real.sqrt (radius v) * (delta v)^2) := by
  have hs : Real.sqrt (radius v) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  rw [Matrix.det_fin_two]
  change
    ((delta v * a 0 0 - v 0 * deltaRow a 0) / (delta v)^2) *
        ((delta v * radialRow a v 1 - radius v * deltaRow a 1) /
          (Real.sqrt (radius v) * (delta v)^2)) -
      ((delta v * a 0 1 - v 0 * deltaRow a 1) / (delta v)^2) *
        ((delta v * radialRow a v 0 - radius v * deltaRow a 0) /
          (Real.sqrt (radius v) * (delta v)^2)) = _
  field_simp [hs, hd]
  simp [augmented, Matrix.det_fin_three, radialRow, deltaRow, radius, delta]
  <;> ring

def affine (v : W) (a : A32) (q : E) : W := v + a.mulVec q

theorem affine_hasFDerivAt (v : W) (a : A32) (q : E) :
    HasFDerivAt (affine v a) a.mulVecLin.toContinuousLinearMap q := by
  exact (a.mulVecLin.toContinuousLinearMap.hasFDerivAt).const_add v

theorem affine_augmented_det (v : W) (a : A32) (q : E) :
    (augmented a (affine v a q)).det = (augmented a v).det := by
  simp [augmented, affine, Matrix.det_fin_three, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  <;> ring

-- Full tangent rank and the sum-one section imply C ≠ 0.
theorem augmented_det_ne_zero (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) : (augmented a v).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.vecMul_injective_iff_isUnit.mp
  intro p q hpq
  change p ᵥ* augmented a v = q ᵥ* augmented a v at hpq
  have hexpand (p : W) : p ᵥ* augmented a v =
      p 0 • v + p 1 • a.col 0 + p 2 • a.col 1 := by
    funext i
    fin_cases i <;>
      simp [augmented, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Matrix.col, smul_eq_mul]
  have h0 : p 0 = q 0 := by
    have h := congrArg S hpq
    rw [hexpand p, hexpand q] at h
    simpa only [map_add, map_smul, hv, hS, smul_eq_mul,
      mul_one, mul_zero, add_zero] using h
  have ht : a.mulVec ![p 1,p 2] = a.mulVec ![q 1,q 2] := by
    funext i
    have h := congrFun hpq i
    rw [hexpand p, hexpand q] at h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.col, smul_eq_mul, h0] at h ⊢
    linarith
  have ht' := ha ht
  funext i
  fin_cases i
  · exact h0
  · exact congrFun ht' 0
  · exact congrFun ht' 1

theorem affine_chart_hasFDerivAt (v : W) (a : A32) (q : E)
    (hr : 0 < radius (affine v a q)) (hd : delta (affine v a q) ≠ 0) :
    HasFDerivAt (fun w => chart (affine v a w))
      (jacobian a (affine v a q)).mulVecLin.toContinuousLinearMap q := by
  apply chart_hasFDerivAt _ _ q _ hr hd
  intro i
  exact hasFDerivAt_pi'.mp (affine_hasFDerivAt v a q) i

theorem affine_jacobian_det (v : W) (a : A32) (q : E)
    (hr : 0 < radius (affine v a q)) (hd : delta (affine v a q) ≠ 0) :
    (jacobian a (affine v a q)).det = (augmented a v).det /
      (Real.sqrt (radius (affine v a q)) * (delta (affine v a q))^2) := by
  rw [jacobian_det a _ hr hd, affine_augmented_det]

theorem jacobian_det_ne_zero (a : A32) (v : W)
    (hr : 0 < radius v) (hd : delta v ≠ 0)
    (hC : (augmented a v).det ≠ 0) : (jacobian a v).det ≠ 0 := by
  rw [jacobian_det a v hr hd]
  exact div_ne_zero hC (mul_ne_zero (Real.sqrt_pos.mpr hr).ne' (pow_ne_zero 2 hd))

theorem chart_height_pos (v : W) (hr : 0 < radius v) (hd : 0 < delta v) :
    0 < chart v 1 := by
  exact div_pos (Real.sqrt_pos.mpr hr) hd

-- The calibrated H2 density factor. This does not identify native surface measure.
theorem jacobian_height_density (a : A32) (v : W)
    (hr : 0 < radius v) (hd : 0 < delta v) :
    |(jacobian a v).det| / (chart v 1)^2 =
      |(augmented a v).det| / (Real.sqrt (radius v))^3 := by
  have hs : 0 < Real.sqrt (radius v) := Real.sqrt_pos.mpr hr
  rw [jacobian_det a v hr hd.ne', abs_div,
    abs_of_pos (mul_pos hs (sq_pos_of_pos hd))]
  change |(augmented a v).det| /
    (Real.sqrt (radius v) * (delta v)^2) /
    (Real.sqrt (radius v) / delta v)^2 = _
  field_simp [hs.ne', hd.ne']
  <;> ring

-- An affine section is identified before using this lemma: it excludes rescaling.
theorem chart_injective_on_section (S : W →ₗ[ℝ] ℝ) :
    Set.InjOn chart {v | 0 < radius v ∧ 0 < delta v ∧ S v = 1} := by
  intro v hv w hw he
  have hx := congrFun he 0
  have hh := congrFun he 1
  change v 0 / delta v = w 0 / delta w at hx
  change Real.sqrt (radius v) / delta v = Real.sqrt (radius w) / delta w at hh
  have ht (u : W) (hu : 0 < radius u) (hd : delta u ≠ 0) :
      (u 2 + u 1) / delta u =
        (Real.sqrt (radius u) / delta u)^2 + (u 0 / delta u)^2 := by
    have hden : u 2 - u 1 ≠ 0 := hd
    dsimp [delta]
    field_simp [hden]
    rw [Real.sq_sqrt hu.le]
    dsimp only [radius]
    ring
  have htw : (v 2 + v 1) / delta v = (w 2 + w 1) / delta w := by
    rw [ht v hv.1 hv.2.1.ne', ht w hw.1 hw.2.1.ne', hh, hx]
  have hn : (delta v)⁻¹ • v = (delta w)⁻¹ • w := by
    funext i
    fin_cases i
    · simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hx
    · have hvd : (v 2 - v 1) / delta v = 1 := div_self hv.2.1.ne'
      have hwd : (w 2 - w 1) / delta w = 1 := div_self hw.2.1.ne'
      simp only [sub_div, add_div] at hvd hwd htw
      change (delta v)⁻¹ * v 1 = (delta w)⁻¹ * w 1
      simp only [div_eq_mul_inv] at hvd hwd htw
      nlinarith [hvd, hwd, htw]
    · have hvd : (v 2 - v 1) / delta v = 1 := div_self hv.2.1.ne'
      have hwd : (w 2 - w 1) / delta w = 1 := div_self hw.2.1.ne'
      simp only [sub_div, add_div] at hvd hwd htw
      change (delta v)⁻¹ * v 2 = (delta w)⁻¹ * w 2
      simp only [div_eq_mul_inv] at hvd hwd htw
      nlinarith [hvd, hwd, htw]
  have hδ : (delta v)⁻¹ = (delta w)⁻¹ := by
    have h := congrArg S hn
    simpa only [map_smul, hv.2.2, hw.2.2, smul_eq_mul, mul_one] using h
  have heδ : delta v = delta w := inv_injective hδ
  funext i
  have h := congrFun hn i
  simp only [Pi.smul_apply, smul_eq_mul, heδ] at h
  exact mul_left_cancel₀ (inv_ne_zero hw.2.1.ne') h

theorem affine_chart_injOn (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) :
    Set.InjOn (fun q => chart (affine v a q))
      {q | 0 < radius (affine v a q) ∧ 0 < delta (affine v a q)} := by
  have hsection (q : E) : S (affine v a q) = 1 := by
    have he : affine v a q = v + q 0 • a.col 0 + q 1 • a.col 1 := by
      funext i
      simp [affine, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.col, smul_eq_mul]
      <;> ring
    rw [he]
    simp only [map_add, map_smul, hv, hS, smul_eq_mul,
      mul_zero, add_zero]
  intro p hp q hq he
  have he' := chart_injective_on_section S
    ⟨hp.1, hp.2, hsection p⟩ ⟨hq.1, hq.2, hsection q⟩ he
  apply ha
  exact add_left_cancel he'

open MeasureTheory Set

-- Equal-dimensional substitution for the actual affine chart, including closed sets.
-- A separate native-Hausdorff density identification is still required.
theorem affine_chart_density_integral (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) (K : Set E) (hK : MeasurableSet K)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hd : ∀ q ∈ K, 0 < delta (affine v a q)) :
    (∫⁻ y in (fun q => chart (affine v a q)) '' K,
      ENNReal.ofReal ((y 1)⁻¹ ^ (2 : ℕ))) =
    ∫⁻ q in K, ENNReal.ofReal
      (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3) := by
  have hf : ∀ q ∈ K, HasFDerivWithinAt (fun w => chart (affine v a w))
      (jacobian a (affine v a q)).mulVecLin.toContinuousLinearMap K q :=
    fun q hq => (affine_chart_hasFDerivAt v a q (hr q hq) (hd q hq).ne').hasFDerivWithinAt
  have hsub : K ⊆ {q | 0 < radius (affine v a q) ∧ 0 < delta (affine v a q)} := by
    intro q hq
    exact ⟨hr q hq, hd q hq⟩
  have hi : InjOn (fun q => chart (affine v a q)) K :=
    Set.InjOn.mono hsub (affine_chart_injOn v a S hv hS ha)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK hf hi]
  apply setLIntegral_congr_fun hK
  intro q hq
  have hdet : ((jacobian a (affine v a q)).mulVecLin.toContinuousLinearMap).det =
      (jacobian a (affine v a q)).det := by
    rw [LinearMap.det_toContinuousLinearMap]
    exact LinearMap.det_toLin' _
  have hprod : |(jacobian a (affine v a q)).det| *
      ((chart (affine v a q) 1)⁻¹)^2 =
      |(augmented a (affine v a q)).det| /
        (Real.sqrt (radius (affine v a q)))^3 := by
    simpa only [div_eq_mul_inv, inv_pow] using
      jacobian_height_density a (affine v a q) (hr q hq) (hd q hq)
  dsimp only
  rw [hdet, ← ENNReal.ofReal_mul (abs_nonneg _), hprod, affine_augmented_det]

end CFMPReflectedPlaneChart435Transient
