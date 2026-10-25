import D5.S3.Geometry.Hyperideal.CFMPOriginalRadialEdgeLength435Transient
import D5.S3.Geometry.Hyperideal.CFMPAffineRadialNativeSpeed435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeCoordinates435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix Interval
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPNativePullbackMetric435Transient
open CFMPOriginalNativeCoordinates435Transient

namespace CFMPOriginalRadialCurveLength435Transient

-- Native coordinate speed along the original coefficient segment.
theorem original_radial_curve_length
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hfinj : Function.Injective f)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (lambda mu : cutBody l) (hne : lambda ≠ mu) :
    let U : ℝ → Fin 4 → ℝ := fun r => ((1-r) • lambda.val+r • mu.val) ᵥ* M
    let v := (mu.val-lambda.val) ᵥ* M
    let curve : ℝ → Fin 3 → ℝ := fun r => nativeMap (U r)
    (∀ (r : ℝ), r ∈ Icc (0 : ℝ) 1 →
      ∃ w : cutBody l, w.val = (1-r) • lambda.val+r • mu.val ∧
        curve r = nativeCoordinates (f w) ∧ 0 < curve r 2 ∧
        HasDerivAt curve ((nativeMatrix (U r)).mulVec v) r) ∧
    (∫ r : ℝ in (0 : ℝ)..1,
      Real.sqrt (dotProduct (deriv curve r) (deriv curve r)/(curve r 2)^2)) =
        dist (f lambda) (f mu) := by
  let Y := lambda.val ᵥ* M
  let Z := mu.val ᵥ* M
  let U : ℝ → Fin 4 → ℝ := fun r => ((1-r) • lambda.val+r • mu.val) ᵥ* M
  let v := (mu.val-lambda.val) ᵥ* M
  let curve : ℝ → Fin 3 → ℝ := fun r => nativeMap (U r)
  let scale (w : cutBody l) := Real.sqrt (-gramQuadratic l w.val)
  let a := scale lambda
  let b := scale mu
  let chi := Real.cosh (dist (f lambda) (f mu))
  let Q (r : ℝ) := a^2*(1-r)^2+2*a*b*chi*r*(1-r)+b^2*r^2
  have hs (w : cutBody l) : 0 < scale w :=
    Real.sqrt_pos.mpr (neg_pos.mpr
      ((shared_radial_body l hl).2.2.2.1 w.val w.property))
  have hraw (w : cutBody l) : w.val ᵥ* M = scale w • lift (f w) := by
    obtain ⟨y,hy,hu,ht,hc⟩ := hf w
    have hw : lift (f w) = (radial l w.val) ᵥ* M :=
      (lift_of_coordinates _ _ hu ht hc).trans hy
    have hr : radial l w.val = (scale w)⁻¹ • w.val := by
      ext i
      simp [radial,scale,div_eq_mul_inv,mul_comm]
    rw [hw,hr,Matrix.smul_vecMul,smul_smul,mul_inv_cancel₀ (hs w).ne',one_smul]
  have hYY : lorentz Y Y = -a^2 := by
    rw [show Y = a • lift (f lambda) from hraw lambda]
    simpa [lift_unit, pow_two] using (lorentz_linear (lift (f lambda)) (lift (f lambda))
      (lift (f lambda)) (lift (f lambda)) a 0 a 0)
  have hZZ : lorentz Z Z = -b^2 := by
    rw [show Z = b • lift (f mu) from hraw mu]
    simpa [lift_unit, pow_two] using (lorentz_linear (lift (f mu)) (lift (f mu))
      (lift (f mu)) (lift (f mu)) b 0 b 0)
  have hYZ : lorentz Y Z = -a*b*chi := by
    rw [show Y = a • lift (f lambda) from hraw lambda,
      show Z = b • lift (f mu) from hraw mu]
    have h := lorentz_linear (lift (f lambda)) (lift (f lambda))
      (lift (f mu)) (lift (f mu)) a 0 b 0
    simp only [zero_smul,add_zero,mul_zero,zero_mul,lift_cosh] at h
    dsimp [chi]
    nlinarith only [h]
  have hchi : 1 < chi :=
    Real.one_lt_cosh.mpr (dist_pos.mpr (fun h => hne (hfinj h))).ne'
  have hconv : Convex ℝ (cutBody l) := by
    rw [← (D5.S3.Geometry.Hyperideal.LengthGramPolytope.cut_body_polytope l hl).2.1]
    exact convex_convexHull ℝ _
  have hmem (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      (1-r) • lambda.val+r • mu.val ∈ cutBody l :=
    hconv lambda.property mu.property (sub_nonneg.mpr hr.2) hr.1 (sub_add_cancel 1 r)
  have hU (r : ℝ) : U r = (1-r) • Y+r • Z := by
    simp only [U,Y,Z,Matrix.add_vecMul,Matrix.smul_vecMul]
  have hv : v = Z-Y := by simp only [v,Y,Z,Matrix.sub_vecMul]
  have hcoord (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      0 < radius (U r) ∧ 0 < delta (U r) ∧
        nativeCoordinates (f ⟨(1-r) • lambda.val+r • mu.val,hmem r hr⟩) = curve r :=
    original_native_coordinates l hl M f hf ⟨_,hmem r hr⟩
  have hD (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      HasDerivAt curve ((nativeMatrix (U r)).mulVec v) r := by
    have hline : HasDerivAt U v r := by
      have h := (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).smul_const Y).add
        ((hasDerivAt_id r).smul_const Z)
      convert h using 1
      · funext s
        exact hU s
      · simp [hv, sub_eq_add_neg, add_comm]
    exact (nativeMap_hasFDerivAt (U r) (hcoord r hr).1
      (hcoord r hr).2.1.ne').comp_hasDerivAt r hline
  have hQ (r : ℝ) : radius (U r) = Q r := by
    rw [hU]
    dsimp only [radius]
    rw [lorentz_linear,hYY,hZZ,hYZ,lorentz_symm Z Y,hYZ]
    dsimp [Q]
    ring
  have hspeed (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      Real.sqrt (dotProduct (deriv curve r) (deriv curve r)/(curve r 2)^2) =
        a*b*Real.sqrt (chi^2-1)/Q r := by
    rw [(hD r hr).deriv]
    have h := CFMPAffineRadialNativeSpeed435Transient.affine_native_squared_speed
      Y Z a b chi r (hs lambda) (hs mu) hchi hYY hZZ hYZ hr
      (by rw [← hU]; exact (hcoord r hr).2.1.ne')
    change dotProduct ((nativeMatrix ((1-r) • Y+r • Z)).mulVec (Z-Y))
      ((nativeMatrix ((1-r) • Y+r • Z)).mulVec (Z-Y)) /
        (nativeMap ((1-r) • Y+r • Z) 2)^2 =
          (a*b*Real.sqrt (chi^2-1)/Q r)^2 at h
    change Real.sqrt (dotProduct ((nativeMatrix (U r)).mulVec v)
      ((nativeMatrix (U r)).mulVec v)/(nativeMap (U r) 2)^2) = _
    rw [hU,hv,h]
    exact Real.sqrt_sq (div_nonneg
      (mul_nonneg (mul_pos (hs lambda) (hs mu)).le (Real.sqrt_nonneg _))
      (by rw [← hQ]; exact (hcoord r hr).1.le))
  refine ⟨?_,?_⟩
  · intro r hr
    refine ⟨⟨_,hmem r hr⟩,rfl,(hcoord r hr).2.2.symm,?_,hD r hr⟩
    change 0 < curve r 2
    rw [← (hcoord r hr).2.2]
    exact (f ⟨_,hmem r hr⟩).coordinates.property
  · calc
      _ = ∫ r : ℝ in (0 : ℝ)..1,a*b*Real.sqrt (chi^2-1)/Q r := by
        apply intervalIntegral.integral_congr
        intro r hr
        exact hspeed r (by simpa using hr)
      _ = Real.arcosh chi :=
        CFMPAffineRadialEdgeLength435Transient.affine_radial_speed_integral
          a b chi (hs lambda) (hs mu) hchi
      _ = _ := Real.arcosh_cosh dist_nonneg

end CFMPOriginalRadialCurveLength435Transient

run_cmd do
  let name := ``CFMPOriginalRadialCurveLength435Transient.original_radial_curve_length
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP469 missing declaration {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP469 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP469 CHECKED {name} axioms={axioms}"
