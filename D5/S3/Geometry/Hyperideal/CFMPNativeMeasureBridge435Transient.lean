import D5.S3.Geometry.HyperbolicNormalizedDensity
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic


noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicNormalizedDensity

namespace CFMPHausdorffNormalization435Transient

open MeasureTheory.Measure

local instance : MeasurableSpace Coordinates3 := borel _
local instance : BorelSpace Coordinates3 := ⟨rfl⟩
local instance : MeasurableSpace Native3 := borel _
local instance : BorelSpace Native3 := ⟨rfl⟩

-- The calibration uses the actual L2 ambient metric.
theorem normalized_native_measure_exists : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    c = (Measure.hausdorffMeasure 3 : Measure (Ambient ℂ))
      (parallelepiped (stdOrthonormalBasis ℝ (Ambient ℂ))) ∧
    (c⁻¹ • rawNativeMeasure).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity := by
  have hdim : Module.finrank ℝ (Ambient ℂ) = 3 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).finrank_eq]
    simp [Module.finrank_prod]
  let μ : Measure (Ambient ℂ) := Measure.hausdorffMeasure 3
  letI : IsAddHaarMeasure μ := by
    dsimp [μ]
    have hdimR : (Module.finrank ℝ (Ambient ℂ) : ℝ) = 3 := by
      exact_mod_cast hdim
    rw [← hdimR]
    infer_instance
  let a : ℝ≥0 := addHaarScalarFactor μ volume
  have ha : 0 < a := addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  let c : ℝ≥0∞ := a
  have hc0 : c ≠ 0 := by
    change (a : ℝ≥0∞) ≠ 0
    simpa using (ne_of_gt ha)
  have hct : c ≠ ∞ := ENNReal.coe_ne_top
  have hA : μ = c • (volume : Measure (Ambient ℂ)) := by
    exact isAddLeftInvariant_eq_smul μ volume
  have hset : MeasurableSet {p : Ambient ℂ | 0 < (WithLp.ofLp p).2} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have he : MeasurableEmbedding (Subtype.val : Coordinates3 → Ambient ℂ) :=
    Topology.IsEmbedding.subtypeVal.measurableEmbedding (by
      simpa only [Subtype.range_val_subtype] using hset)
  have hraw : rawCoordinateMeasure =
      μ.comap (Subtype.val : Coordinates3 → Ambient ℂ) := by
    ext s hs
    rw [Measure.comap_apply _ Subtype.val_injective
      (fun u hu => he.measurableSet_image.mpr hu) _ hs]
    exact (isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num)) s).symm
  have hcal : rawCoordinateMeasure = c •
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)) := by
    rw [hraw, hA, Measure.comap_smul]
  have hcube : μ (parallelepiped (stdOrthonormalBasis ℝ (Ambient ℂ))) = c := by
    rw [hA, Measure.smul_apply,
      (stdOrthonormalBasis ℝ (Ambient ℂ)).volume_parallelepiped]
    simp
  refine ⟨c, hc0, hct, hcube.symm, ?_⟩
  rw [Measure.map_smul _ coordinatesEquiv.measurable.aemeasurable, raw_native_density, hcal, withDensity_smul_measure,
    smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

end CFMPHausdorffNormalization435Transient


set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody

namespace CFMPActualGramJacobian435Transient

abbrev V := Fin 3 → ℝ
abbrev W := Fin 4 → ℝ
abbrev A43 := Matrix (Fin 4) (Fin 3) ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

def delta (u : W) : ℝ := u 3 - u 2

def radius (u : W) : ℝ := -lorentz u u

def deltaRow (a : A43) (j : Fin 3) : ℝ := a 3 j - a 2 j

def radialRow (a : A43) (u : W) (j : Fin 3) : ℝ :=
  -u 0 * a 0 j - u 1 * a 1 j - u 2 * a 2 j + u 3 * a 3 j

def augmented (a : A43) (u : W) : M4 :=
  !![a 0 0,a 0 1,a 0 2,u 0;
     a 1 0,a 1 1,a 1 2,u 1;
     a 2 0,a 2 1,a 2 2,u 2;
     a 3 0,a 3 1,a 3 2,u 3]

def rowTransform (u : W) : M4 :=
  !![1,0,0,0; 0,1,0,0; -u 0,-u 1,-u 2,u 3; 0,0,-1,1]

def numerator (a : A43) (u : W) : M3 := fun i j =>
  if i = 0 then delta u * a 0 j - u 0 * deltaRow a j
  else if i = 1 then delta u * a 1 j - u 1 * deltaRow a j
  else delta u * radialRow a u j - radius u * deltaRow a j

def jacobian (a : A43) (u : W) : M3 := fun i j =>
  if i = 0 then numerator a u i j / (delta u)^2
  else if i = 1 then numerator a u i j / (delta u)^2
  else numerator a u i j / (Real.sqrt (radius u) * (delta u)^2)

-- The last-column Schur complement uses the actual null-coordinate denominator.
-- This temporary identity is a direct application of pinned matrix determinant results.
theorem numerator_det (a : A43) (u : W) (hd : delta u ≠ 0) :
    (numerator a u).det = (delta u)^3 * (augmented a u).det := by
  norm_num [numerator, delta, deltaRow, radialRow, radius, lorentz,
    augmented, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Fin.sum_univ_four, Fin.sum_univ_three, Fin.succAbove]
  <;> ring

theorem jacobian_det (a : A43) (u : W)
    (hr : 0 < radius u) (hd : delta u ≠ 0) :
    (jacobian a u).det = (augmented a u).det /
      (Real.sqrt (radius u) * (delta u)^3) := by
  let v : V := ![((delta u)^2)⁻¹, ((delta u)^2)⁻¹,
    (Real.sqrt (radius u) * (delta u)^2)⁻¹]
  have he : jacobian a u = Matrix.of (fun i j => v i * numerator a u i j) := by
    ext i j
    fin_cases i <;> simp [jacobian,v,div_eq_mul_inv,mul_comm]
  rw [he,Matrix.det_mul_column,numerator_det a u hd]
  have hs : Real.sqrt (radius u) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  simp [v,Fin.prod_univ_three]
  <;> field_simp [hd,hs]
  <;> ring

def lift3 (z : V) : W := ![z 0,z 1,z 2,1-z 0-z 1-z 2]

def framePoint (M : M4) (z : V) : W := (lift3 z) ᵥ* M

def frameDifferential (M : M4) : A43 :=
  fun i j => M j.castSucc i - M 3 i

def sumOneFrame (z : V) : M4 :=
  !![1,0,0,z 0; 0,1,0,z 1; 0,0,1,z 2; -1,-1,-1,1-z 0-z 1-z 2]

theorem actual_augmented_det (M : M4) (z : V) :
    (augmented (frameDifferential M) (framePoint M z)).det = M.det := by
  have hP : (sumOneFrame z).det = 1 := by
    norm_num [sumOneFrame,Matrix.det_succ_row_zero,Matrix.det_fin_three,
      Fin.sum_univ_four,Fin.sum_univ_three,Fin.succAbove]
    <;> ring
  have h : augmented (frameDifferential M) (framePoint M z) =
      M.transpose * sumOneFrame z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [augmented,frameDifferential,framePoint,lift3,sumOneFrame,
        Matrix.vecMul,dotProduct,Matrix.mul_apply,Fin.sum_univ_four]
    <;> ring
  rw [h,Matrix.det_mul,Matrix.det_transpose,hP,mul_one]

theorem actual_gram_chart_jacobian (M : M4) (z : V)
    (hr : 0 < radius (framePoint M z))
    (hd : delta (framePoint M z) ≠ 0) :
    (jacobian (frameDifferential M) (framePoint M z)).det = M.det /
      (Real.sqrt (radius (framePoint M z)) * (delta (framePoint M z))^3) := by
  rw [jacobian_det _ _ hr hd,actual_augmented_det]


def coordinateChart (u : W) : V :=
  ![u 0 / delta u, u 1 / delta u, Real.sqrt (radius u) / delta u]

def rowMap (a : A43) (i : Fin 4) : V →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp a.mulVecLin.toContinuousLinearMap

def radialMap (a : A43) (u : W) : V →L[ℝ] ℝ :=
  -(u 0 • rowMap a 0) - u 1 • rowMap a 1 - u 2 • rowMap a 2 + u 3 • rowMap a 3

-- The derivative is proved for the displayed chart, not supplied as a premise.
theorem coordinateChart_hasFDerivAt (f : V → W) (a : A43) (z : V)
    (hf : ∀ i, HasFDerivAt (fun w => f w i) (rowMap a i) z)
    (hr : 0 < radius (f z)) (hd : delta (f z) ≠ 0) :
    HasFDerivAt (fun w => coordinateChart (f w))
      (jacobian a (f z)).mulVecLin.toContinuousLinearMap z := by
  have hdelta : HasFDerivAt (fun w => delta (f w))
      (rowMap a 3 - rowMap a 2) z := (hf 3).sub (hf 2)
  have hinv := (hasDerivAt_inv hd).comp_hasFDerivAt z hdelta
  have hrad : HasFDerivAt (fun w => radius (f w))
      (2 • radialMap a (f z)) z := by
    have h := (((((hf 0).mul (hf 0)).add ((hf 1).mul (hf 1))).add
      ((hf 2).mul (hf 2))).sub ((hf 3).mul (hf 3))).neg
    convert h using 1
    · funext w
      simp [radius,lorentz,Fin.sum_univ_four]
      <;> ring
    · ext w
      simp [radialMap,smul_eq_mul]
      <;> ring
  have hroot := hrad.sqrt (ne_of_gt hr)
  have hs : Real.sqrt (radius (f z)) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hsq := Real.sq_sqrt hr.le
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert (hf 0).mul hinv using 1
    · funext w
      simp [coordinateChart,div_eq_mul_inv]
    · ext w
      simp [jacobian,numerator,rowMap,deltaRow,Matrix.mulVec,dotProduct,
        Fin.sum_univ_three,smul_eq_mul]
      <;> field_simp [hd]
      <;> ring
  · convert (hf 1).mul hinv using 1
    · funext w
      simp [coordinateChart,div_eq_mul_inv]
    · ext w
      simp [jacobian,numerator,rowMap,deltaRow,Matrix.mulVec,dotProduct,
        Fin.sum_univ_three,smul_eq_mul]
      <;> field_simp [hd]
      <;> ring
  · convert hroot.mul hinv using 1
    · funext w
      simp [coordinateChart,div_eq_mul_inv]
    · ext w
      simp [jacobian,numerator,rowMap,radialMap,radialRow,deltaRow,
        Matrix.mulVec,dotProduct,Fin.sum_univ_three,smul_eq_mul]
      <;> field_simp [hd,hs]
      <;> ring_nf
      <;> simp only [hsq]
      <;> ring

theorem framePoint_hasFDerivAt (M : M4) (z : V) :
    HasFDerivAt (framePoint M) (frameDifferential M).mulVecLin.toContinuousLinearMap z := by
  have hfun : framePoint M = fun w => M 3 + (frameDifferential M).mulVec w := by
    funext w i
    fin_cases i <;>
      simp [framePoint,lift3,frameDifferential,Matrix.vecMul,Matrix.mulVec,
        dotProduct,Fin.sum_univ_four,Fin.sum_univ_three]
    <;> ring
  rw [hfun]
  exact ((frameDifferential M).mulVecLin.toContinuousLinearMap.hasFDerivAt).const_add (M 3)

theorem actual_coordinateChart_hasFDerivAt (M : M4) (z : V)
    (hr : 0 < radius (framePoint M z)) (hd : delta (framePoint M z) ≠ 0) :
    HasFDerivAt (fun w => coordinateChart (framePoint M w))
      (jacobian (frameDifferential M) (framePoint M z)).mulVecLin.toContinuousLinearMap z := by
  apply coordinateChart_hasFDerivAt _ _ z _ hr hd
  intro i
  exact hasFDerivAt_pi'.mp (framePoint_hasFDerivAt M z) i


theorem actual_radius_eq (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (z : V) :
    radius (framePoint M z) = -gramQuadratic l (lift3 z) := by
  unfold radius gramQuadratic
  simp_rw [← hg]
  simp [framePoint,lorentz,Matrix.vecMul,dotProduct,Fin.sum_univ_four]
  <;> ring

theorem actual_frame_det_square (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) :
    -(lengthGram l).det = M.det^2 := by
  let J : M4 := Matrix.diagonal ![(1 : ℝ),1,1,-1]
  have hG : M * J * M.transpose = lengthGram l := by
    ext i j
    simpa [J,Matrix.mul_apply,lorentz,Fin.sum_univ_four] using hg i j
  have hJ : J.det = -1 := by
    simp [J,Matrix.det_diagonal,Fin.prod_univ_four]
  rw [← hG,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hJ]
  ring

theorem actual_frame_sqrt_det (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hM : 0 < M.det) : Real.sqrt (-(lengthGram l).det) = M.det := by
  rw [actual_frame_det_square M l hg,Real.sqrt_sq_eq_abs,abs_of_pos hM]

-- This is the pointwise density product needed by change of variables.
-- No equality of measures or native-volume variation is assumed or concluded here.
theorem actual_height_jacobian_product (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hM : 0 < M.det) (z : V)
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
    abs_of_pos (div_pos hM (mul_pos hs (pow_pos hd 3))),
    actual_frame_sqrt_det M l hg hM,← actual_radius_eq M l hg z]
  simp [coordinateChart]
  <;> field_simp [ne_of_gt hr,ne_of_gt hs,ne_of_gt hd]
  <;> ring_nf
  <;> simp only [hfour,hsq]
  <;> ring


open MeasureTheory Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicTopology

-- This is the explicit original real-triple/complex-height coordinate map.
def encodeEquiv : V ≃ᵐ Ambient ℂ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    (MeasurableEquiv.prodComm.trans
      ((Complex.measurableEquivPi.symm.prodCongr (MeasurableEquiv.refl ℝ)).trans
        (MeasurableEquiv.toLp 2 (ℂ × ℝ))))

theorem encodeEquiv_apply (z : V) :
    encodeEquiv z = WithLp.toLp 2 (Complex.mk (z 0) (z 1), z 2) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply Complex.ext <;>
      simp [encodeEquiv, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
        MeasurableEquiv.prodCongr, Complex.measurableEquivPi_symm_apply,
        Fin.succAbove, Fin.insertNthEquiv, Fin.removeNth]
  · rfl

theorem encodeEquiv_preserving : MeasurePreserving encodeEquiv := by
  exact (WithLp.volume_preserving_toLp ℂ ℝ).comp
    (((MeasurePreserving.symm Complex.measurableEquivPi
      Complex.volume_preserving_equiv_pi).prod
      (MeasurePreserving.id (volume : Measure ℝ))).comp
      (Measure.measurePreserving_swap.comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)))

def chartDomain (l : Fin 6 → ℝ) : Set V := {z | lift3 z ∈ cutBody l}

theorem frame_normalization (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (z : V) (i : Fin 4) :
    ((radial l (lift3 z)) ᵥ* M) i =
      framePoint M z i / Real.sqrt (radius (framePoint M z)) := by
  rw [actual_radius_eq M l hg z]
  simp only [radial, framePoint, Matrix.vecMul, dotProduct]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]

-- hcoord is exactly the coordinate witness supplied by shared_radial_body.
theorem original_native_coordinates (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (z : V) (hr : 0 < radius (framePoint M z)) (p : HyperbolicThreeSpace)
    (hcoord : p.coordinates.val = WithLp.toLp 2
      (Complex.mk
        (((radial l (lift3 z)) ᵥ* M) 0 /
          (((radial l (lift3 z)) ᵥ* M) 3 - ((radial l (lift3 z)) ᵥ* M) 2))
        (((radial l (lift3 z)) ᵥ* M) 1 /
          (((radial l (lift3 z)) ᵥ* M) 3 - ((radial l (lift3 z)) ᵥ* M) 2)),
       1 / (((radial l (lift3 z)) ᵥ* M) 3 - ((radial l (lift3 z)) ᵥ* M) 2))) :
    0 < delta (framePoint M z) ∧
      p.coordinates.val = encodeEquiv (coordinateChart (framePoint M z)) := by
  have hs : 0 < Real.sqrt (radius (framePoint M z)) := Real.sqrt_pos.mpr hr
  have hden : ((radial l (lift3 z)) ᵥ* M) 3 -
      ((radial l (lift3 z)) ᵥ* M) 2 =
      delta (framePoint M z) / Real.sqrt (radius (framePoint M z)) := by
    rw [frame_normalization M l hg z 3, frame_normalization M l hg z 2]
    simp only [delta, sub_div]
  have hpos : 0 < 1 / (((radial l (lift3 z)) ᵥ* M) 3 -
      ((radial l (lift3 z)) ᵥ* M) 2) := by
    have hp := p.coordinates.property
    rw [hcoord] at hp
    exact hp
  have hd : 0 < delta (framePoint M z) := by
    have hp := one_div_pos.mp hpos
    rw [hden] at hp
    exact (div_pos_iff_of_pos_right hs).mp hp
  refine ⟨hd, ?_⟩
  rw [hcoord, encodeEquiv_apply]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · apply Complex.ext <;>
      simp [coordinateChart, frame_normalization M l hg z, delta]
    <;> have hd0 : framePoint M z 3 - framePoint M z 2 ≠ 0 := hd.ne'
    <;> field_simp [hs.ne', hd.ne', hd0]
    <;> ring
  · simp [coordinateChart, hden]
    <;> field_simp [hs.ne', hd.ne']
    <;> ring

theorem actual_chart_injective (M : M4) (l : Fin 6 → ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (hf : Function.Injective f)
    (hc : ∀ z : chartDomain l,
      (f ⟨lift3 z.val, z.property⟩).coordinates.val =
        encodeEquiv (coordinateChart (framePoint M z.val))) :
    InjOn (fun z => coordinateChart (framePoint M z)) (chartDomain l) := by
  intro z hz w hw he
  have hcoords : (f ⟨lift3 z, hz⟩).coordinates.val =
      (f ⟨lift3 w, hw⟩).coordinates.val := by
    rw [hc ⟨z,hz⟩, hc ⟨w,hw⟩]
    exact congrArg encodeEquiv he
  have hnative : f ⟨lift3 z, hz⟩ = f ⟨lift3 w, hw⟩ :=
    (coordinatesHomeomorph (E := ℂ)).injective (Subtype.ext hcoords)
  have hlift : lift3 z = lift3 w := congrArg Subtype.val (hf hnative)
  ext i
  fin_cases i
  · simpa [lift3] using congrFun hlift 0
  · simpa [lift3] using congrFun hlift 1
  · simpa [lift3] using congrFun hlift 2

theorem chartDomain_measurable (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    MeasurableSet (chartDomain l) := by
  have hc : Continuous lift3 := by unfold lift3; fun_prop
  exact ((shared_radial_body l hl).1.isClosed.preimage hc).measurableSet

-- Exact change of variables for the same chart; native-measure calibration is separate.
theorem actual_chart_density_integral (M : M4) (l : Fin 6 → ℝ)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hM : 0 < M.det) (s : Set V) (hs : MeasurableSet s)
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
    actual_height_jacobian_product M l hg hM z (hr z hz) (hd z hz)]

end CFMPActualGramJacobian435Transient

namespace CFMPNativeMeasureBridge435Transient
open MeasureTheory Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicNormalizedDensity
open D5.S3.Geometry.HyperbolicTopology
open CFMPActualGramJacobian435Transient

local instance : MeasurableSpace Coordinates3 := borel _
local instance : BorelSpace Coordinates3 := ⟨rfl⟩
local instance : MeasurableSpace Native3 := borel _
local instance : BorelSpace Native3 := ⟨rfl⟩

def ambientHeightDensity (p : Ambient ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((WithLp.ofLp p).2)⁻¹ ^ (3 : ℕ))

theorem calibrated_native_set (c : ℝ≥0∞)
    (hcal : (c⁻¹ • rawNativeMeasure).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity)
    (s : Set Coordinates3) (hs : MeasurableSet s) :
    (c⁻¹ • rawNativeMeasure) (coordinatesEquiv ⁻¹' s) =
      ∫⁻ p in (Subtype.val : Coordinates3 → Ambient ℂ) '' s, ambientHeightDensity p := by
  have hP : MeasurableSet {p : Ambient ℂ | 0 < (WithLp.ofLp p).2} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  rw [← Measure.map_apply coordinatesEquiv.measurable hs, hcal, withDensity_apply _ hs]
  have he : MeasurableEmbedding (Subtype.val : Coordinates3 → Ambient ℂ) :=
    Topology.IsEmbedding.subtypeVal.measurableEmbedding (by simpa only [Subtype.range_val_subtype] using hP)
  change (∫⁻ p in s, ambientHeightDensity p.val ∂((volume : Measure (Ambient ℂ)).comap Subtype.val)) = _
  rw [he.restrict_comap, ← he.lintegral_map, he.map_comap,
    Measure.restrict_restrict he.measurableSet_range]
  have hsub : (Subtype.val : Coordinates3 → Ambient ℂ) '' s ⊆
      {p : Ambient ℂ | 0 < (WithLp.ofLp p).2} := by
    rintro p ⟨x,hx,rfl⟩
    exact x.property
  rw [Subtype.range_val_subtype, inter_eq_right.mpr hsub]

def drop3 (x : W) : V := fun i => x i.castSucc

theorem lift3_drop3 (x : W) (hx : ∑ i, x i = 1) : lift3 (drop3 x) = x := by
  have hs : x 0 + x 1 + x 2 + x 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hx
  ext i
  fin_cases i <;> simp [drop3,lift3]
  <;> linarith

theorem actual_native_ambient_image (M : M4) (l : Fin 6 → ℝ)
    (f : cutBody l → HyperbolicThreeSpace)
    (hc : ∀ z : chartDomain l,
      (f ⟨lift3 z.val,z.property⟩).coordinates.val =
        encodeEquiv (coordinateChart (framePoint M z.val))) :
    range (fun v : cutBody l => (f v).coordinates.val) =
      encodeEquiv '' ((fun z => coordinateChart (framePoint M z)) '' chartDomain l) := by
  apply Subset.antisymm
  · rintro p ⟨v,rfl⟩
    let z : V := drop3 v.val
    have hv : lift3 z = v.val := lift3_drop3 v.val v.property.1.2
    have hz : z ∈ chartDomain l := by
      change lift3 z ∈ cutBody l
      rw [hv]
      exact v.property
    have hsub : (⟨lift3 z,hz⟩ : cutBody l) = v := Subtype.ext hv
    refine ⟨coordinateChart (framePoint M z),⟨z,hz,rfl⟩,?_⟩
    rw [← hc ⟨z,hz⟩, hsub]
  · rintro p ⟨_,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨⟨lift3 z,hz⟩,?_⟩
    exact hc ⟨z,hz⟩

-- The supplied f and coordinate witness are exactly the original realization interface.
theorem actual_native_volume (c : ℝ≥0∞)
    (hcal : (c⁻¹ • rawNativeMeasure).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity)
    (M : M4) (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hg : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (hM : 0 < M.det)
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
      actual_chart_density_integral M l hg hM (chartDomain l)
        (chartDomain_measurable l hl) hr (fun z hz => (hc ⟨z,hz⟩).1)
        (actual_chart_injective M l f hfi (fun z => (hc z).2))


-- Direct application to the original genuine six-length realization, with no new frame premise.
example (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (hgen : let c := fun k : Fin 6 => Real.cosh (l k);
      -1 < D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
        (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) ∧
      D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
        (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) < 1) :
    ∃ (c : ℝ≥0∞) (M : M4) (f : cutBody l → HyperbolicThreeSpace),
      c ≠ 0 ∧ c ≠ ∞ ∧
      c = (Measure.hausdorffMeasure 3 : Measure (Ambient ℂ))
        (parallelepiped (stdOrthonormalBasis ℝ (Ambient ℂ))) ∧
      (∀ i j, lorentz (M i) (M j) = lengthGram l i j) ∧ 0 < M.det ∧
      Continuous f ∧ Function.Injective f ∧ IsCompact (range f) ∧
      (range f).Nonempty ∧
      (c⁻¹ • rawNativeMeasure) (range f) =
        ∫⁻ z in chartDomain l, ENNReal.ofReal
          (Real.sqrt (-(lengthGram l).det) / (-gramQuadratic l (lift3 z))^2) := by
  obtain ⟨M,hg,hM,_,f,hf,hfi,hcompact,hne,hsource⟩ :=
    (shared_radial_body l hl).2.2.2.2.2.2.2.2.2 hgen
  obtain ⟨c,hc0,hct,hcube,hcal⟩ :=
    CFMPHausdorffNormalization435Transient.normalized_native_measure_exists
  refine ⟨c,M,f,hc0,hct,hcube,hg,hM,hf,hfi,hcompact,hne,?_⟩
  exact actual_native_volume c hcal M l hl hg hM f hfi hcompact hsource

end CFMPNativeMeasureBridge435Transient
