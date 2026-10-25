import D5.S3.Geometry.Hyperideal.CFMPAffineRadialEdgeLength435Transient
import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix Interval
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace CFMPOriginalRadialEdgeLength435Transient

-- The scalar normalization uses the actual native endpoint distance.
theorem lifted_endpoints_speed_integral
    (p q : HyperbolicThreeSpace) (hpq : p ≠ q)
    (Y Z : Fin 4 → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hY : Y = a • lift p) (hZ : Z = b • lift q) :
    let chi := -lorentz Y Z / (a*b)
    (∫ r : ℝ in (0 : ℝ)..1,
      a*b*Real.sqrt (chi^2-1) /
        (a^2*(1-r)^2 + 2*a*b*chi*r*(1-r) + b^2*r^2)) = dist p q := by
  dsimp only
  have hB : lorentz Y Z = a*b*(-Real.cosh (dist p q)) := by
    rw [hY,hZ]
    simpa only [zero_smul,add_zero,mul_zero,zero_mul,lift_cosh] using
      (lorentz_linear (lift p) (lift p) (lift q) (lift q) a 0 b 0)
  have hchi : -lorentz Y Z / (a*b) = Real.cosh (dist p q) := by
    rw [hB]
    field_simp [ha.ne',hb.ne']
    <;> ring
  rw [hchi]
  rw [CFMPAffineRadialEdgeLength435Transient.affine_radial_speed_integral
    a b _ ha hb (Real.one_lt_cosh.mpr (dist_pos.mpr hpq).ne')]
  exact Real.arcosh_cosh dist_nonneg

-- The raw endpoints come from the same supplied original M/f contract.
theorem original_endpoints_speed_integral
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hfinj : Function.Injective f)
    (hframe : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (lambda mu : cutBody l) (hne : lambda ≠ mu) :
    let a := Real.sqrt (-gramQuadratic l lambda.val)
    let b := Real.sqrt (-gramQuadratic l mu.val)
    let chi := -lorentz (lambda.val ᵥ* M) (mu.val ᵥ* M) / (a*b)
    (∫ r : ℝ in (0 : ℝ)..1,
      a*b*Real.sqrt (chi^2-1) /
        (a^2*(1-r)^2 + 2*a*b*chi*r*(1-r) + b^2*r^2)) =
      dist (f lambda) (f mu) := by
  let scale (v : cutBody l) := Real.sqrt (-gramQuadratic l v.val)
  have hs (v : cutBody l) : 0 < scale v :=
    Real.sqrt_pos.mpr (neg_pos.mpr
      ((shared_radial_body l hl).2.2.2.1 v.val v.property))
  have hraw (v : cutBody l) : v.val ᵥ* M = scale v • lift (f v) := by
    obtain ⟨y,hy,hu,ht,hc⟩ := hframe v
    have hv : lift (f v) = (radial l v.val) ᵥ* M :=
      (lift_of_coordinates _ _ hu ht hc).trans hy
    have hr : radial l v.val = (scale v)⁻¹ • v.val := by
      ext i
      simp [radial,scale,div_eq_mul_inv,mul_comm]
    rw [hv,hr,Matrix.smul_vecMul,smul_smul,mul_inv_cancel₀ (hs v).ne',one_smul]
  exact lifted_endpoints_speed_integral (f lambda) (f mu)
    (fun h => hne (hfinj h)) (lambda.val ᵥ* M) (mu.val ᵥ* M)
    (scale lambda) (scale mu) (hs lambda) (hs mu) (hraw lambda) (hraw mu)

end CFMPOriginalRadialEdgeLength435Transient
