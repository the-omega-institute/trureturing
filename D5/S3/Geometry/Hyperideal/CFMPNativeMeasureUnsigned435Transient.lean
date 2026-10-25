import D5.S3.Geometry.Hyperideal.CFMPNativeTwentyCellVolume435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Matrix BigOperators NNReal ENNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicNormalizedDensity
open D5.S3.Geometry.HyperbolicTopology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPActualGramJacobian435Transient
open CFMPNativeMeasureBridge435Transient

namespace CFMPNativeMeasureUnsigned435Transient
local instance : MeasurableSpace Coordinates3 := borel _
local instance : BorelSpace Coordinates3 := ⟨rfl⟩
local instance : MeasurableSpace Native3 := borel _
local instance : BorelSpace Native3 := ⟨rfl⟩

theorem height_jacobian_product_unsigned (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (z : V)
    (hr : 0 < radius (framePoint M z)) (hd : 0 < delta (framePoint M z)) :
    |(jacobian (frameDifferential M) (framePoint M z)).det| *
        ((coordinateChart (framePoint M z) 2)⁻¹)^3 =
      Real.sqrt (-(lengthGram l).det) /
        (-gramQuadratic l (lift3 z))^2 := by
  have hs : 0 < Real.sqrt (radius (framePoint M z)) := Real.sqrt_pos.mpr hr
  have hsq := Real.sq_sqrt hr.le
  have hfour : (Real.sqrt (radius (framePoint M z)))^4 =
      (radius (framePoint M z))^2 := by
    calc
      _ = ((Real.sqrt (radius (framePoint M z)))^2)^2 := by ring
      _ = _ := by rw [hsq]
  rw [actual_gram_chart_jacobian M z hr hd.ne',
    abs_div,abs_of_pos (mul_pos hs (pow_pos hd 3)),
    actual_frame_det_square M l hg,Real.sqrt_sq_eq_abs,← actual_radius_eq M l hg z]
  simp [coordinateChart]
  <;> field_simp [ne_of_gt hr,ne_of_gt hs,ne_of_gt hd]
  <;> ring_nf
  <;> simp only [hfour,hsq]
  <;> ring

theorem chart_density_integral_unsigned (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (s : Set V) (hs : MeasurableSet s)
    (hr : ∀ z ∈ s, 0 < radius (framePoint M z))
    (hd : ∀ z ∈ s, 0 < delta (framePoint M z))
    (hi : InjOn (fun z => coordinateChart (framePoint M z)) s) :
    (∫⁻ y in (fun z => coordinateChart (framePoint M z)) '' s,
      ENNReal.ofReal ((y 2)⁻¹ ^ (3 : ℕ))) =
    ∫⁻ z in s, ENNReal.ofReal
      (Real.sqrt (-(lengthGram l).det) / (-gramQuadratic l (lift3 z))^2) := by
  have hf : ∀ z ∈ s, HasFDerivWithinAt
      (fun w => coordinateChart (framePoint M w))
      (jacobian (frameDifferential M) (framePoint M z)).mulVecLin.toContinuousLinearMap
      s z := fun z hz => (actual_coordinateChart_hasFDerivAt M z
        (hr z hz) (hd z hz).ne').hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf hi]
  apply setLIntegral_congr_fun hs
  intro z hz
  have hdet :
      ((jacobian (frameDifferential M) (framePoint M z)).mulVecLin.toContinuousLinearMap).det =
        (jacobian (frameDifferential M) (framePoint M z)).det := by
    rw [LinearMap.det_toContinuousLinearMap]
    exact LinearMap.det_toLin' _
  dsimp only
  rw [hdet, ← ENNReal.ofReal_mul (abs_nonneg _),
    height_jacobian_product_unsigned M l hg z (hr z hz) (hd z hz)]

theorem native_volume_unsigned (c : ℝ≥0∞)
    (hcal : (c⁻¹ • rawNativeMeasure).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity)
    (M : M4) (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace) (hfi : Function.Injective f)
    (hcompact : IsCompact (range f))
    (hsource : ∀ v : cutBody l, ∃ y : W,
      y = (radial l v.val) ᵥ* M ∧ lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)),1/(y 3-y 2))) :
    (c⁻¹ • rawNativeMeasure) (range f) =
      ∫⁻ z in chartDomain l, ENNReal.ofReal
        (Real.sqrt (-(lengthGram l).det) / (-gramQuadratic l (lift3 z))^2) := by
  have hr : ∀ z ∈ chartDomain l, 0 < radius (framePoint M z) := by
    intro z hz
    rw [actual_radius_eq M l hg z]
    exact neg_pos.mpr ((shared_radial_body l hl).2.2.2.1 (lift3 z) hz)
  have hc : ∀ z : chartDomain l, 0 < delta (framePoint M z.val) ∧
      (f ⟨lift3 z.val,z.property⟩).coordinates.val =
        encodeEquiv (coordinateChart (framePoint M z.val)) := by
    intro z
    obtain ⟨y,hy,_,_,hcoord⟩ := hsource ⟨lift3 z.val,z.property⟩
    rw [hy] at hcoord
    exact original_native_coordinates M l hg z.val (hr z.val z.property)
      (f ⟨lift3 z.val,z.property⟩) hcoord
  let s : Set Coordinates3 := coordinatesEquiv '' range f
  have hs : MeasurableSet s := by
    have hK : IsCompact s :=
      hcompact.image (coordinatesHomeomorph (E := ℂ)).continuous
    exact hK.measurableSet
  have hpre : coordinatesEquiv ⁻¹' s = range f :=
    preimage_image_eq _ coordinatesEquiv.injective
  have himage : (Subtype.val : Coordinates3 → Ambient ℂ) '' s =
      encodeEquiv '' ((fun z => coordinateChart (framePoint M z)) '' chartDomain l) := by
    change (Subtype.val : Coordinates3 → Ambient ℂ) ''
      (coordinatesEquiv '' range f) = _
    rw [image_image,← Set.range_comp']
    exact actual_native_ambient_image M l f (fun z => (hc z).2)
  calc
    (c⁻¹ • rawNativeMeasure) (range f) =
        (c⁻¹ • rawNativeMeasure) (coordinatesEquiv ⁻¹' s) := by rw [hpre]
    _ = ∫⁻ p in (Subtype.val : Coordinates3 → Ambient ℂ) '' s,
        ambientHeightDensity p := calibrated_native_set c hcal s hs
    _ = ∫⁻ z in (fun z => coordinateChart (framePoint M z)) '' chartDomain l,
        ENNReal.ofReal ((z 2)⁻¹ ^ (3 : ℕ)) := by
      rw [himage]
      have hm := encodeEquiv_preserving.setLIntegral_comp_emb
        encodeEquiv.measurableEmbedding ambientHeightDensity
        ((fun z => coordinateChart (framePoint M z)) '' chartDomain l)
      simpa only [ambientHeightDensity,encodeEquiv_apply,WithLp.ofLp_toLp] using hm.symm
    _ = ∫⁻ z in chartDomain l, ENNReal.ofReal
        (Real.sqrt (-(lengthGram l).det) / (-gramQuadratic l (lift3 z))^2) :=
      chart_density_integral_unsigned M l hg (chartDomain l)
        (chartDomain_measurable l hl) hr (fun z hz => (hc ⟨z,hz⟩).1)
        (actual_chart_injective M l f hfi (fun z => (hc z).2))

end CFMPNativeMeasureUnsigned435Transient
