/- GID: D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorMetric
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CyclicHyperbolicSectorMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.AddCircle, mathlib/module/Mathlib.Analysis.Complex.Isometry]
   utility: none
   digest: Original finite chains attain the capped angular metric in numbered actual hyperbolic sectors. -/

import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import D5.S3.Geometry.HyperbolicSupportBoundary
import D5.S3.Topology.FiniteOrbitChainMetric
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix NNReal ENNReal
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric

set_option autoImplicit false

private def cylinderLift (rho z theta : ℝ) : Fin 4 → ℝ :=
  ![Real.sinh rho * Real.cos theta, Real.sinh rho * Real.sin theta,
    Real.cosh rho * Real.sinh z, Real.cosh rho * Real.cosh z]

private theorem cylinder_unit (rho z theta : ℝ) :
    lorentz (cylinderLift rho z theta) (cylinderLift rho z theta) = -1 := by
  calc
    _ = Real.sinh rho ^ 2 * (Real.sin theta ^ 2 + Real.cos theta ^ 2) -
        Real.cosh rho ^ 2 * (Real.cosh z ^ 2 - Real.sinh z ^ 2) := by
      simp only [cylinderLift, lorentz, Fin.sum_univ_succ, Fin.sum_univ_zero]
      dsimp
      ring
    _ = -1 := by
      rw [Real.sin_sq_add_cos_sq, Real.cosh_sq_sub_sinh_sq]
      nlinarith [Real.cosh_sq_sub_sinh_sq rho]

def cylindricalPoint (rho z theta : ℝ) : HyperbolicThreeSpace :=
  project (cylinderLift rho z theta) (cylinder_unit rho z theta)
    (by change 0 < Real.cosh rho * Real.cosh z; positivity)

private theorem cylindrical_lift (rho z theta : ℝ) :
    lift (cylindricalPoint rho z theta) = cylinderLift rho z theta :=
  lift_of_coordinates _ _ (cylinder_unit rho z theta)
    (by change 0 < Real.cosh rho * Real.cosh z; positivity) rfl

private theorem cylindrical_cosh_distance (rho z theta sigma w phi : ℝ) :
    Real.cosh (dist (cylindricalPoint rho z theta) (cylindricalPoint sigma w phi)) =
      Real.cosh rho * Real.cosh sigma * Real.cosh (z - w) -
      Real.sinh rho * Real.sinh sigma * Real.cos (theta - phi) := by
  apply neg_injective
  calc
    _ = lorentz (lift (cylindricalPoint rho z theta))
        (lift (cylindricalPoint sigma w phi)) :=
      (lift_cosh _ _).symm
    _ = _ := by
      rw [cylindrical_lift, cylindrical_lift]
      simp [cylinderLift, lorentz, Fin.sum_univ_succ, Real.cosh_sub, Real.cos_sub]
      <;> ring

private theorem cylindrical_axis (z theta : ℝ) :
    cylindricalPoint 0 z theta = cylindricalPoint 0 z 0 := by
  apply lift_injective
  simp [cylindrical_lift, cylinderLift]

private def transverse (p : HyperbolicThreeSpace) : ℂ :=
  ⟨lift p 0, lift p 1⟩

def radialCoordinate (p : HyperbolicThreeSpace) : ℝ :=
  Real.arsinh ‖transverse p‖

def axialCoordinate (p : HyperbolicThreeSpace) : ℝ :=
  Real.arsinh (lift p 2 / Real.cosh (radialCoordinate p))

def angularCoordinate (p : HyperbolicThreeSpace) : ℝ :=
  (transverse p).arg

private theorem cylindrical_reconstruct (p : HyperbolicThreeSpace) :
    cylindricalPoint (radialCoordinate p) (axialCoordinate p) (angularCoordinate p) = p := by
  apply lift_injective
  rw [cylindrical_lift]
  have hr : Real.sinh (radialCoordinate p) = ‖transverse p‖ :=
    Real.sinh_arsinh _
  have hz : Real.sinh (axialCoordinate p) =
      lift p 2 / Real.cosh (radialCoordinate p) := Real.sinh_arsinh _
  have hc : Real.cosh (radialCoordinate p) ≠ 0 := (Real.cosh_pos _).ne'
  have hnorm : ‖transverse p‖ ^ 2 = lift p 0 ^ 2 + lift p 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, transverse, pow_two]
  have hunit := lift_unit p
  simp [lorentz, Fin.sum_univ_succ] at hunit
  ext k
  fin_cases k
  · simpa [cylinderLift, hr, angularCoordinate, transverse] using
      Complex.norm_mul_cos_arg (transverse p)
  · simpa [cylinderLift, hr, angularCoordinate, transverse] using
      Complex.norm_mul_sin_arg (transverse p)
  · change Real.cosh (radialCoordinate p) * Real.sinh (axialCoordinate p) = lift p 2
    rw [hz]
    exact mul_div_cancel₀ (lift p 2) hc
  · change Real.cosh (radialCoordinate p) * Real.cosh (axialCoordinate p) = lift p 3
    have htime := lift_time p
    have hpos : 0 < Real.cosh (radialCoordinate p) * Real.cosh (axialCoordinate p) :=
      mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
    have hsq : (Real.cosh (radialCoordinate p) * Real.cosh (axialCoordinate p)) ^ 2 =
        (lift p 3) ^ 2 := by
      rw [mul_pow, Real.cosh_sq' (axialCoordinate p), hz, div_pow, mul_add, mul_one,
        mul_div_cancel₀ _ (pow_ne_zero 2 hc), Real.cosh_sq' (radialCoordinate p), hr, hnorm]
      nlinarith [hunit]
    nlinarith

private theorem cylindrical_angle_contraction (rho z theta sigma w phi beta gamma : ℝ)
    (hr : 0 ≤ rho) (hs : 0 ≤ sigma)
    (hangle : |beta - gamma| ≤ |theta - phi|)
    (hsmall : |theta - phi| ≤ Real.pi) :
    dist (cylindricalPoint rho z beta) (cylindricalPoint sigma w gamma) ≤
      dist (cylindricalPoint rho z theta) (cylindricalPoint sigma w phi) := by
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [cylindrical_cosh_distance, cylindrical_cosh_distance]
  have hc : Real.cos (theta - phi) ≤ Real.cos (beta - gamma) := by
    rw [← Real.cos_abs (theta - phi), ← Real.cos_abs (beta - gamma)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hsmall hangle
  have hp : 0 ≤ Real.sinh rho * Real.sinh sigma :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.sinh_nonneg_iff.mpr hs)
  nlinarith [mul_le_mul_of_nonneg_left hc hp]

private def foldedAngle (A reference theta : ℝ) : ℝ :=
  min Real.pi ‖((theta - reference : ℝ) : AddCircle A)‖

private theorem folded_angle_contraction (A reference theta phi : ℝ) :
    |foldedAngle A reference theta - foldedAngle A reference phi| ≤ |theta - phi| := by
  have hcap := ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_min
    Real.pi).dist_le_mul
      ‖((theta - reference : ℝ) : AddCircle A)‖
      ‖((phi - reference : ℝ) : AddCircle A)‖
  have hnorm := abs_norm_sub_norm_le
    ((theta - reference : ℝ) : AddCircle A)
    ((phi - reference : ℝ) : AddCircle A)
  have hquot : ‖((theta - phi : ℝ) : AddCircle A)‖ ≤ |theta - phi| := by
    simpa only [Real.norm_eq_abs] using
      (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples A)
        (m := theta - phi))
  have hd : ((theta - reference : ℝ) : AddCircle A) -
      ((phi - reference : ℝ) : AddCircle A) = ((theta - phi : ℝ) : AddCircle A) := by
    simp only [AddCircle.coe_sub]
    abel
  rw [hd] at hnorm
  have hcap' : |foldedAngle A reference theta - foldedAngle A reference phi| ≤
      |‖((theta - reference : ℝ) : AddCircle A)‖ -
        ‖((phi - reference : ℝ) : AddCircle A)‖| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq, foldedAngle] using hcap
  exact hcap'.trans (hnorm.trans hquot)

private def mapUpper (e : ℂ → ℂ) (p : UpperHalfSpace ℂ) : UpperHalfSpace ℂ :=
  ⟨WithLp.toLp 2 (e p.val.fst, height p), p.property⟩

private theorem map_upper_distance (e : ℂ ≃ₗᵢ[ℝ] ℂ) (p q : UpperHalfSpace ℂ) :
    hyperbolicDist (mapUpper e p) (mapUpper e q) = hyperbolicDist p q := by
  have he : dist ((mapUpper e p).val : Ambient ℂ) (mapUpper e q).val =
      dist (p.val : Ambient ℂ) q.val := by
    rw [WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
    simp [mapUpper, height, e.isometry.dist_eq]
  simp only [hyperbolicDist, he]
  rfl

private def horizontalIso (e : ℂ ≃ₗᵢ[ℝ] ℂ) :
    HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace where
  toFun p := ⟨mapUpper e p.coordinates⟩
  invFun p := ⟨mapUpper e.symm p.coordinates⟩
  left_inv p := by
    cases p with
    | mk p =>
      change HyperbolicSpace.mk _ = HyperbolicSpace.mk _
      congr 1
      apply Subtype.ext
      apply WithLp.ofLp_injective
      apply Prod.ext
      · simp [mapUpper]
      · rfl
  right_inv p := by
    cases p with
    | mk p =>
      change HyperbolicSpace.mk _ = HyperbolicSpace.mk _
      congr 1
      apply Subtype.ext
      apply WithLp.ofLp_injective
      apply Prod.ext
      · simp [mapUpper]
      · rfl
  isometry_toFun := Isometry.of_dist_eq fun p q =>
    map_upper_distance e p.coordinates q.coordinates

private def turn (theta : ℝ) : HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace :=
  horizontalIso (_root_.rotation (Circle.exp theta))

private theorem turn_lift (theta : ℝ) (p : HyperbolicThreeSpace) :
    lift (turn theta p) =
      ![Real.cos theta * lift p 0 - Real.sin theta * lift p 1,
        Real.sin theta * lift p 0 + Real.cos theta * lift p 1,
        lift p 2, lift p 3] := by
  let e := _root_.rotation (Circle.exp theta)
  have hnorm : (e p.coordinates.val.fst).re ^ 2 +
      (e p.coordinates.val.fst).im ^ 2 =
      p.coordinates.val.fst.re ^ 2 + p.coordinates.val.fst.im ^ 2 := by
    have h : Complex.normSq (e p.coordinates.val.fst) =
        Complex.normSq p.coordinates.val.fst := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, e.norm_map]
    simpa only [Complex.normSq_apply, ← pow_two] using h
  have hre : (e p.coordinates.val.fst).re =
      Real.cos theta * p.coordinates.val.fst.re -
        Real.sin theta * p.coordinates.val.fst.im := by
    simp [e, Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have him : (e p.coordinates.val.fst).im =
      Real.sin theta * p.coordinates.val.fst.re +
        Real.cos theta * p.coordinates.val.fst.im := by
    simp [e, Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  ext k
  fin_cases k
  · change (e p.coordinates.val.fst).re / height p.coordinates = _
    rw [hre]
    change (Real.cos theta * p.coordinates.val.fst.re -
      Real.sin theta * p.coordinates.val.fst.im) / height p.coordinates =
      Real.cos theta * (p.coordinates.val.fst.re / height p.coordinates) -
        Real.sin theta * (p.coordinates.val.fst.im / height p.coordinates)
    ring
  · change (e p.coordinates.val.fst).im / height p.coordinates = _
    rw [him]
    change (Real.sin theta * p.coordinates.val.fst.re +
      Real.cos theta * p.coordinates.val.fst.im) / height p.coordinates =
      Real.sin theta * (p.coordinates.val.fst.re / height p.coordinates) +
        Real.cos theta * (p.coordinates.val.fst.im / height p.coordinates)
    ring
  · change (((e p.coordinates.val.fst).re ^ 2 + (e p.coordinates.val.fst).im ^ 2 +
        height p.coordinates ^ 2 - 1) / (2 * height p.coordinates)) = lift p 2
    rw [hnorm]
    rfl
  · change (((e p.coordinates.val.fst).re ^ 2 + (e p.coordinates.val.fst).im ^ 2 +
        height p.coordinates ^ 2 + 1) / (2 * height p.coordinates)) = lift p 3
    rw [hnorm]
    rfl

private theorem turn_cancel (theta : ℝ) (p : HyperbolicThreeSpace) :
    turn (-theta) (turn theta p) = p := by
  apply lift_injective
  rw [turn_lift, turn_lift]
  ext k
  fin_cases k <;> simp [Real.cos_neg, Real.sin_neg]
  · linear_combination (lift p 0) * (Real.sin_sq_add_cos_sq theta)
  · linear_combination (lift p 1) * (Real.sin_sq_add_cos_sq theta)

private theorem turn_transverse (theta : ℝ) (p : HyperbolicThreeSpace) :
    transverse (turn theta p) = _root_.rotation (Circle.exp theta) (transverse p) := by
  apply Complex.ext
  · simp [transverse, turn_lift, Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  · simp [transverse, turn_lift, Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring

private theorem turn_radial (theta : ℝ) (p : HyperbolicThreeSpace) :
    radialCoordinate (turn theta p) = radialCoordinate p := by
  simp only [radialCoordinate, turn_transverse, LinearIsometryEquiv.norm_map]

private theorem turn_axial (theta : ℝ) (p : HyperbolicThreeSpace) :
    axialCoordinate (turn theta p) = axialCoordinate p := by
  simp only [axialCoordinate, turn_radial, turn_lift, Matrix.cons_val]

def sector (alpha : ℝ) : Set HyperbolicThreeSpace :=
  {p | 0 ≤ lift p 1 ∧
    Real.cos alpha * lift p 1 - Real.sin alpha * lift p 0 ≤ 0}

private theorem sector_angle (alpha : ℝ) (ha : 0 < alpha)
    (p : sector alpha) : angularCoordinate p.val ∈ Icc 0 alpha := by
  have harg : 0 ≤ angularCoordinate p.val :=
    Complex.arg_nonneg_iff.mpr p.property.1
  refine ⟨harg, ?_⟩
  by_cases hv : transverse p.val = 0
  · simpa [angularCoordinate, hv] using ha.le
  have hnorm : 0 < ‖transverse p.val‖ := norm_pos_iff.mpr hv
  have hx := Complex.norm_mul_cos_arg (transverse p.val)
  have hy := Complex.norm_mul_sin_arg (transverse p.val)
  have hbound : ‖transverse p.val‖ *
      Real.sin (angularCoordinate p.val - alpha) ≤ 0 := by
    rw [Real.sin_sub]
    change ‖transverse p.val‖ *
      (Real.sin (transverse p.val).arg * Real.cos alpha -
        Real.cos (transverse p.val).arg * Real.sin alpha) ≤ 0
    calc
      _ = Real.cos alpha * lift p.val 1 - Real.sin alpha * lift p.val 0 := by
        change _ = Real.cos alpha * (transverse p.val).im -
          Real.sin alpha * (transverse p.val).re
        rw [← hx, ← hy]
        ring
      _ ≤ 0 := p.property.2
  by_contra hn
  have hdiff : 0 < angularCoordinate p.val - alpha := sub_pos.mpr (lt_of_not_ge hn)
  have hdiffpi : angularCoordinate p.val - alpha < Real.pi :=
    sub_lt_self _ ha |>.trans_le (Complex.arg_le_pi _)
  exact (not_lt_of_ge hbound)
    (mul_pos hnorm (Real.sin_pos_of_pos_of_lt_pi hdiff hdiffpi))

private theorem sector_fold_nonexpanding (alpha A reference offset : ℝ)
    (ha : 0 < alpha) (hapi : alpha < Real.pi) (p q : sector alpha) :
    dist
      (cylindricalPoint (radialCoordinate p.val) (axialCoordinate p.val)
        (foldedAngle A reference (offset + angularCoordinate p.val)))
      (cylindricalPoint (radialCoordinate q.val) (axialCoordinate q.val)
        (foldedAngle A reference (offset + angularCoordinate q.val))) ≤ dist p q := by
  have hp := sector_angle alpha ha p
  have hq := sector_angle alpha ha q
  have hang : |angularCoordinate p.val - angularCoordinate q.val| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  have hfold := folded_angle_contraction A reference
    (offset + angularCoordinate p.val) (offset + angularCoordinate q.val)
  rw [add_sub_add_left_eq_sub] at hfold
  have h := cylindrical_angle_contraction
    (radialCoordinate p.val) (axialCoordinate p.val) (angularCoordinate p.val)
    (radialCoordinate q.val) (axialCoordinate q.val) (angularCoordinate q.val)
    (foldedAngle A reference (offset + angularCoordinate p.val))
    (foldedAngle A reference (offset + angularCoordinate q.val))
    (Real.arsinh_nonneg_iff.mpr (norm_nonneg _))
    (Real.arsinh_nonneg_iff.mpr (norm_nonneg _)) hfold hang
  simpa only [cylindrical_reconstruct, Subtype.dist_eq] using h

private def upperFace (alpha : ℝ) : Set (sector alpha) :=
  {p | Real.cos alpha * lift p.val 1 - Real.sin alpha * lift p.val 0 = 0}

private def lowerFace (alpha : ℝ) : Set (sector alpha) :=
  {p | lift p.val 1 = 0}

private theorem upper_rotates_to_lower (alpha beta : ℝ)
    (ha : 0 < alpha) (hapi : alpha < Real.pi)
    (hb : 0 < beta) (hbpi : beta < Real.pi)
    (p : upperFace alpha) :
    turn (-alpha) p.val.val ∈ sector beta ∧
      lift (turn (-alpha) p.val.val) 1 = 0 := by
  have hs : 0 < Real.sin alpha := Real.sin_pos_of_pos_of_lt_pi ha hapi
  have hsb : 0 ≤ Real.sin beta :=
    (Real.sin_pos_of_pos_of_lt_pi hb hbpi).le
  have hy : lift (turn (-alpha) p.val.val) 1 = 0 := by
    rw [turn_lift]
    have hp : Real.cos alpha * lift p.val.val 1 - Real.sin alpha * lift p.val.val 0 = 0 := p.property
    change Real.sin (-alpha) * lift p.val.val 0 + Real.cos (-alpha) * lift p.val.val 1 = 0
    rw [Real.sin_neg, Real.cos_neg]
    linarith [hp]
  have hx : 0 ≤ lift (turn (-alpha) p.val.val) 0 := by
    have heq : Real.sin alpha * lift (turn (-alpha) p.val.val) 0 = lift p.val.val 1 := by
      rw [turn_lift]
      simp only [Matrix.cons_val, Real.cos_neg, Real.sin_neg, neg_mul, sub_neg_eq_add]
      have hp : Real.cos alpha * lift p.val.val 1 - Real.sin alpha * lift p.val.val 0 = 0 := p.property
      linear_combination -(Real.cos alpha) * hp +
        (lift p.val.val 1) * (Real.sin_sq_add_cos_sq alpha)
    exact (mul_nonneg_iff_of_pos_left hs).mp (heq.symm ▸ p.val.property.1)
  exact ⟨⟨by simp [hy], by simpa [hy] using neg_nonpos.mpr (mul_nonneg hsb hx)⟩, hy⟩

private theorem lower_rotates_to_upper (alpha beta : ℝ)
    (ha : 0 < alpha) (hapi : alpha < Real.pi)
    (hb : 0 < beta) (hbpi : beta < Real.pi)
    (p : lowerFace beta) :
    turn alpha p.val.val ∈ sector alpha ∧
      Real.cos alpha * lift (turn alpha p.val.val) 1 -
        Real.sin alpha * lift (turn alpha p.val.val) 0 = 0 := by
  have hs : 0 ≤ Real.sin alpha :=
    (Real.sin_pos_of_pos_of_lt_pi ha hapi).le
  have hsb : 0 < Real.sin beta := Real.sin_pos_of_pos_of_lt_pi hb hbpi
  have hx : 0 ≤ lift p.val.val 0 := by
    have h := p.val.property.2
    rw [p.property, mul_zero, zero_sub] at h
    exact (mul_nonneg_iff_of_pos_left hsb).mp (neg_nonpos.mp h)
  have heq : Real.cos alpha * lift (turn alpha p.val.val) 1 -
      Real.sin alpha * lift (turn alpha p.val.val) 0 = 0 := by
    rw [turn_lift]
    have hp : lift p.val.val 1 = 0 := p.property
    simp only [Matrix.cons_val, hp, mul_zero,
      add_zero, sub_zero]
    ring
  refine ⟨⟨?_, heq.le⟩, heq⟩
  rw [turn_lift]
  have hp : lift p.val.val 1 = 0 := p.property
  simpa only [Matrix.cons_val, hp, mul_zero, add_zero] using mul_nonneg hs hx

private def seamEquiv (alpha beta : ℝ)
    (ha : 0 < alpha) (hapi : alpha < Real.pi)
    (hb : 0 < beta) (hbpi : beta < Real.pi) :
    upperFace alpha ≃ᵢ lowerFace beta where
  toFun p :=
    let h := upper_rotates_to_lower alpha beta ha hapi hb hbpi p
    ⟨⟨turn (-alpha) p.val.val, h.1⟩, h.2⟩
  invFun p :=
    let h := lower_rotates_to_upper alpha beta ha hapi hb hbpi p
    ⟨⟨turn alpha p.val.val, h.1⟩, h.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [neg_neg] using turn_cancel (-alpha) p.val.val
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact turn_cancel alpha p.val.val
  isometry_toFun := Isometry.of_dist_eq fun p q =>
    (turn (-alpha)).isometry.dist_eq p.val.val q.val.val

private def sectorDatum {I : Type*} (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi) :
    D5.S3.Topology.FiniteOrbitChainMetric.Datum I I (fun i => sector (alpha i)) where
  src i := i
  dst := next
  dom i := upperFace (alpha i)
  ran i := lowerFace (alpha (next i))
  iso i := seamEquiv (alpha i) (alpha (next i)) (ha i) (hapi i) (ha (next i)) (hapi (next i))
  closed_dom i := by
    have hc : Continuous (fun p : sector (alpha i) => lift p.val) :=
      D5.S3.Geometry.HyperbolicSupportBoundary.lift_continuous.comp continuous_subtype_val
    exact isClosed_eq
      ((continuous_const.mul ((continuous_apply 1).comp hc)).sub
        (continuous_const.mul ((continuous_apply 0).comp hc))) continuous_const
  closed_ran i := by
    have hc : Continuous (fun p : sector (alpha (next i)) => lift p.val) :=
      D5.S3.Geometry.HyperbolicSupportBoundary.lift_continuous.comp continuous_subtype_val
    exact isClosed_eq ((continuous_apply 1).comp hc) continuous_const

private def fold {I : Type*} (alpha : I → ℝ) (A reference : ℝ) (offset : I → ℝ)
    (p : Sigma (fun i => sector (alpha i))) : HyperbolicThreeSpace :=
  cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val)
    (foldedAngle A reference (offset p.1 + angularCoordinate p.2.val))

private theorem lower_face_angle (alpha : ℝ) (ha : 0 < alpha) (hapi : alpha < Real.pi)
    (p : lowerFace alpha) : angularCoordinate p.val.val = 0 := by
  apply Complex.arg_eq_zero_iff.mpr
  refine ⟨?_, p.property⟩
  have h := p.val.property.2
  rw [p.property, mul_zero, zero_sub] at h
  exact (mul_nonneg_iff_of_pos_left
    (Real.sin_pos_of_pos_of_lt_pi ha hapi)).mp (neg_nonpos.mp h)

private theorem upper_face_angle (alpha : ℝ) (ha : 0 < alpha) (hapi : alpha < Real.pi)
    (p : upperFace alpha) (hv : transverse p.val.val ≠ 0) :
    angularCoordinate p.val.val = alpha := by
  have htheta := sector_angle alpha ha p.val
  have hnorm : 0 < ‖transverse p.val.val‖ := norm_pos_iff.mpr hv
  have hx := Complex.norm_mul_cos_arg (transverse p.val.val)
  have hy := Complex.norm_mul_sin_arg (transverse p.val.val)
  have hzero : ‖transverse p.val.val‖ * Real.sin (alpha - angularCoordinate p.val.val) = 0 := by
    rw [Real.sin_sub]
    change ‖transverse p.val.val‖ *
      (Real.sin alpha * Real.cos (transverse p.val.val).arg -
        Real.cos alpha * Real.sin (transverse p.val.val).arg) = 0
    calc
      _ = -(Real.cos alpha * lift p.val.val 1 - Real.sin alpha * lift p.val.val 0) := by
        change _ = -(Real.cos alpha * (transverse p.val.val).im -
          Real.sin alpha * (transverse p.val.val).re)
        rw [← hx, ← hy]
        ring
      _ = 0 := by rw [p.property, neg_zero]
  apply le_antisymm htheta.2
  by_contra hn
  have hd : 0 < alpha - angularCoordinate p.val.val := sub_pos.mpr (lt_of_not_ge hn)
  have hdpi : alpha - angularCoordinate p.val.val < Real.pi := by linarith [htheta.1]
  exact (ne_of_gt (mul_pos hnorm (Real.sin_pos_of_pos_of_lt_pi hd hdpi))) hzero

private def runWidth {I : Type*} (next : I → I) (alpha : I → ℝ)
    (i : I) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, alpha (next^[k] i)

private theorem runWidth_zero {I : Type*} (next : I → I) (alpha : I → ℝ) (i : I) :
    runWidth next alpha i 0 = 0 := by
  simp only [runWidth, Finset.range_zero, Finset.sum_empty]

private theorem runWidth_succ {I : Type*} (next : I → I) (alpha : I → ℝ)
    (i : I) (m : ℕ) :
    runWidth next alpha i (m + 1) = alpha i + runWidth next alpha (next i) m := by
  unfold runWidth
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  exact add_comm _ _

private theorem runWidth_nonneg {I : Type*} (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (i : I) (m : ℕ) :
    0 ≤ runWidth next alpha i m := by
  exact Finset.sum_nonneg (fun k _ => (ha (next^[k] i)).le)

private theorem turn_cylindrical (theta rho z phi : ℝ) :
    turn theta (cylindricalPoint rho z phi) =
      cylindricalPoint rho z (theta + phi) := by
  apply lift_injective
  rw [turn_lift, cylindrical_lift, cylindrical_lift]
  ext k
  fin_cases k <;>
    simp [cylinderLift, Real.cos_add, Real.sin_add] <;> ring

private theorem cylindrical_wall (rho z theta beta : ℝ) :
    Real.cos beta * lift (cylindricalPoint rho z theta) 1 -
      Real.sin beta * lift (cylindricalPoint rho z theta) 0 =
        Real.sinh rho * Real.sin (theta - beta) := by
  simp only [cylindrical_lift, cylinderLift, Matrix.cons_val]
  rw [Real.sin_sub]
  ring

private theorem cylindrical_dot (rho z theta phi : ℝ) :
    Real.cos phi * lift (cylindricalPoint rho z theta) 0 +
      Real.sin phi * lift (cylindricalPoint rho z theta) 1 =
        Real.sinh rho * Real.cos (theta - phi) := by
  simp only [cylindrical_lift, cylinderLift, Matrix.cons_val]
  rw [Real.cos_sub]
  ring

private theorem cylindrical_mem_sector (rho z theta beta : ℝ)
    (hr : 0 ≤ rho) (hb : 0 < beta) (hbpi : beta < Real.pi)
    (htheta : theta ∈ Icc 0 beta) :
    cylindricalPoint rho z theta ∈ sector beta := by
  have hs : 0 ≤ Real.sinh rho := Real.sinh_nonneg_iff.mpr hr
  change 0 ≤ lift (cylindricalPoint rho z theta) 1 ∧
    Real.cos beta * lift (cylindricalPoint rho z theta) 1 -
      Real.sin beta * lift (cylindricalPoint rho z theta) 0 ≤ 0
  constructor
  · have hsin : 0 ≤ Real.sin theta :=
      Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 (htheta.2.trans hbpi.le)
    simpa only [cylindrical_lift, cylinderLift, Matrix.cons_val] using
      mul_nonneg hs hsin
  · rw [cylindrical_wall]
    have hsin : 0 ≤ Real.sin (beta - theta) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [htheta.2])
        (by linarith [htheta.1])
    have hneg : Real.sin (theta - beta) ≤ 0 := by
      rw [show theta - beta = -(beta - theta) by ring, Real.sin_neg]
      exact neg_nonpos.mpr hsin
    exact mul_nonpos_of_nonneg_of_nonpos hs hneg


private theorem strict_wall_crossing
    (rp z tp rq w T beta : ℝ)
    (hrp : 0 < rp) (hrq : 0 < rq)
    (hb : 0 < beta) (hbpi : beta < Real.pi)
    (htp : tp < beta) (hT : beta < T) (hshort : T - tp < Real.pi) :
    ∃ r s : ℝ, 0 < r ∧
      dist (cylindricalPoint rp z tp) (cylindricalPoint r s beta) +
        dist (cylindricalPoint r s beta) (cylindricalPoint rq w T) =
          dist (cylindricalPoint rp z tp) (cylindricalPoint rq w T) := by
  let P := cylindricalPoint rp z tp
  let Q := cylindricalPoint rq w T
  have hsrp : 0 < Real.sinh rp := Real.sinh_pos_iff.mpr hrp
  have hsrq : 0 < Real.sinh rq := Real.sinh_pos_iff.mpr hrq
  have hwallP : Real.cos beta * lift P 1 - Real.sin beta * lift P 0 < 0 := by
    change Real.cos beta * lift (cylindricalPoint rp z tp) 1 -
      Real.sin beta * lift (cylindricalPoint rp z tp) 0 < 0
    rw [cylindrical_wall]
    have hsin : 0 < Real.sin (beta - tp) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [show tp - beta = -(beta - tp) by ring, Real.sin_neg]
    exact mul_neg_of_pos_of_neg hsrp (neg_neg_of_pos hsin)
  have hwallQ : 0 < Real.cos beta * lift Q 1 - Real.sin beta * lift Q 0 := by
    change 0 < Real.cos beta * lift (cylindricalPoint rq w T) 1 -
      Real.sin beta * lift (cylindricalPoint rq w T) 0
    rw [cylindrical_wall]
    exact mul_pos hsrq
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hpq : P ≠ Q := by
    intro he
    rw [he] at hwallP
    linarith
  obtain ⟨gamma, hiso, hzero, hend, hgamma, hbetween⟩ :=
    D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.hyperbolic_segment P Q hpq
  let D := dist P Q
  have hD : 0 < D := dist_pos.mpr hpq
  have hsD : 0 < Real.sinh D := Real.sinh_pos_iff.mpr hD
  let a : ℝ → ℝ := fun t => Real.sinh (D - t) / Real.sinh D
  let b : ℝ → ℝ := fun t => Real.sinh t / Real.sinh D
  let F : ℝ → ℝ := fun t =>
    a t * (Real.cos beta * lift P 1 - Real.sin beta * lift P 0) +
      b t * (Real.cos beta * lift Q 1 - Real.sin beta * lift Q 0)
  have hF : Continuous F := by
    dsimp [F, a, b]
    fun_prop
  have hFzero : F 0 < 0 := by
    simpa only [F, a, b, sub_zero, Real.sinh_zero, div_self hsD.ne', zero_div,
      one_mul, zero_mul, add_zero] using hwallP
  have hFend : 0 < F D := by
    simpa only [F, a, b, sub_self, Real.sinh_zero, zero_div, div_self hsD.ne',
      zero_mul, one_mul, zero_add] using hwallQ
  obtain ⟨t, ht, hFt⟩ :=
    intermediate_value_Icc hD.le hF.continuousOn ⟨hFzero.le, hFend.le⟩
  let R := gamma ⟨t, ht⟩
  have hlift : lift R = a t • lift P + b t • lift Q := by
    simpa only [R, a, b, D,
      D5.S3.Geometry.Hyperideal.LengthGramMetricSegments.interpolate] using
        hgamma ⟨t, ht⟩
  have hwall : Real.cos beta * lift R 1 - Real.sin beta * lift R 0 = 0 := by
    calc
      _ = F t := by
        rw [hlift]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        dsimp only [F]
        ring
      _ = 0 := hFt
  have hat : 0 ≤ a t :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith [ht.2])) hsD.le
  have hbt : 0 ≤ b t :=
    div_nonneg (Real.sinh_nonneg_iff.mpr ht.1) hsD.le
  have hab : 0 < a t + b t := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have hap : 0 < a t :=
        div_pos (Real.sinh_pos_iff.mpr (by linarith)) hsD
      linarith
    · have hbp : 0 < b t := by
        dsimp only [b]
        rw [heq]
        exact div_pos hsD hsD
      linarith
  let mid := (tp + T) / 2
  have hcosP : 0 < Real.cos (tp - mid) :=
    Real.cos_pos_of_mem_Ioo ⟨by dsimp only [mid]; linarith,
      by dsimp only [mid]; linarith⟩
  have hcosQ : 0 < Real.cos (T - mid) :=
    Real.cos_pos_of_mem_Ioo ⟨by dsimp only [mid]; linarith,
      by dsimp only [mid]; linarith⟩
  have hdotP : 0 < Real.cos mid * lift P 0 + Real.sin mid * lift P 1 := by
    change 0 < Real.cos mid * lift (cylindricalPoint rp z tp) 0 +
      Real.sin mid * lift (cylindricalPoint rp z tp) 1
    rw [cylindrical_dot]
    exact mul_pos hsrp hcosP
  have hdotQ : 0 < Real.cos mid * lift Q 0 + Real.sin mid * lift Q 1 := by
    change 0 < Real.cos mid * lift (cylindricalPoint rq w T) 0 +
      Real.sin mid * lift (cylindricalPoint rq w T) 1
    rw [cylindrical_dot]
    exact mul_pos hsrq hcosQ
  have hdot : 0 < Real.cos mid * lift R 0 + Real.sin mid * lift R 1 := by
    have he : Real.cos mid * lift R 0 + Real.sin mid * lift R 1 =
        a t * (Real.cos mid * lift P 0 + Real.sin mid * lift P 1) +
          b t * (Real.cos mid * lift Q 0 + Real.sin mid * lift Q 1) := by
      rw [hlift]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    rcases lt_or_eq_of_le hat with hap | haz
    · exact add_pos_of_pos_of_nonneg (mul_pos hap hdotP)
        (mul_nonneg hbt hdotQ.le)
    · have hbp : 0 < b t := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg hat hdotP.le) (mul_pos hbp hdotQ)
  let L := Real.cos beta * lift R 0 + Real.sin beta * lift R 1
  have hx : lift R 0 = Real.cos beta * L := by
    dsimp only [L]
    linear_combination -(lift R 0) * (Real.sin_sq_add_cos_sq beta) -
      Real.sin beta * hwall
  have hy : lift R 1 = Real.sin beta * L := by
    dsimp only [L]
    linear_combination -(lift R 1) * (Real.sin_sq_add_cos_sq beta) +
      Real.cos beta * hwall
  have hmidwall : Real.cos mid * lift R 0 + Real.sin mid * lift R 1 =
      Real.cos (mid - beta) * L := by
    calc
      _ = (Real.cos mid * Real.cos beta + Real.sin mid * Real.sin beta) * L := by
        linear_combination Real.cos mid * hx + Real.sin mid * hy
      _ = _ := by rw [Real.cos_sub]
  have hcoswall : 0 < Real.cos (mid - beta) :=
    Real.cos_pos_of_mem_Ioo ⟨by dsimp only [mid]; linarith,
      by dsimp only [mid]; linarith⟩
  have hL : 0 < L := by
    rw [hmidwall] at hdot
    exact (mul_pos_iff_of_pos_left hcoswall).mp hdot
  have hypos : 0 < lift R 1 := by
    rw [hy]
    exact mul_pos (Real.sin_pos_of_pos_of_lt_pi hb hbpi) hL
  have hmem : R ∈ sector beta := ⟨hypos.le, hwall.le⟩
  have hv : transverse R ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    change lift R 1 = 0 at him
    linarith
  have hr : 0 < radialCoordinate R :=
    Real.arsinh_pos_iff.mpr (norm_pos_iff.mpr hv)
  let RU : upperFace beta := ⟨⟨R, hmem⟩, hwall⟩
  have hangle := upper_face_angle beta hb hbpi RU hv
  change angularCoordinate R = beta at hangle
  have hrec : cylindricalPoint (radialCoordinate R) (axialCoordinate R) beta = R := by
    simpa only [hangle] using cylindrical_reconstruct R
  have hsplit : dist P R + dist R Q = dist P Q := by
    have hR : R ∈ range gamma := ⟨⟨t, ht⟩, rfl⟩
    rw [hbetween] at hR
    exact hR
  refine ⟨radialCoordinate R, axialCoordinate R, hr, ?_⟩
  rw [hrec]
  exact hsplit


private theorem short_angle_forward_run {I : Type*}
    (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (m : ℕ) (i : I) (rp z tp rq w tq : ℝ)
    (hrp : 0 < rp) (hrq : 0 < rq)
    (htp : tp ∈ Icc 0 (alpha i))
    (htq : tq ∈ Icc 0 (alpha (next^[m] i)))
    (hspan0 : 0 ≤ runWidth next alpha i m + tq - tp)
    (hspanpi : runWidth next alpha i m + tq - tp < Real.pi) :
    (sectorDatum next alpha ha hapi).Chain
      ⟨i, ⟨cylindricalPoint rp z tp,
        cylindrical_mem_sector rp z tp (alpha i) hrp.le (ha i) (hapi i) htp⟩⟩
      ⟨next^[m] i, ⟨cylindricalPoint rq w tq,
        cylindrical_mem_sector rq w tq (alpha (next^[m] i))
          hrq.le (ha _) (hapi _) htq⟩⟩
      (ENNReal.ofReal (dist (cylindricalPoint rp z tp)
        (cylindricalPoint rq w (runWidth next alpha i m + tq)))) := by
  induction m generalizing i rp z tp rq w tq with
  | zero =>
      let p : sector (alpha i) :=
        ⟨cylindricalPoint rp z tp,
          cylindrical_mem_sector rp z tp (alpha i) hrp.le (ha i) (hapi i) htp⟩
      have hq : tq ∈ Icc 0 (alpha i) := by
        simpa only [Function.iterate_zero_apply] using htq
      let q : sector (alpha i) :=
        ⟨cylindricalPoint rq w tq,
          cylindrical_mem_sector rq w tq (alpha i) hrq.le (ha i) (hapi i) hq⟩
      have hpaid :=
        D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.move (G := sectorDatum next alpha ha hapi) (a := ⟨i, p⟩) p q
          (D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.nil
            (G := sectorDatum next alpha ha hapi) (a := ⟨i, p⟩))
      simpa only [runWidth_zero, Function.iterate_zero_apply, zero_add,
        edist_dist, Subtype.dist_eq, p, q] using hpaid
  | succ m ih =>
      let G := sectorDatum next alpha ha hapi
      let beta := alpha i
      let V := runWidth next alpha (next i) m
      let T := beta + V + tq
      let j := next^[m] (next i)
      have hq : tq ∈ Icc 0 (alpha j) := by
        simpa only [j, Function.iterate_succ_apply] using htq
      let p : sector (alpha i) :=
        ⟨cylindricalPoint rp z tp,
          cylindrical_mem_sector rp z tp (alpha i) hrp.le (ha i) (hapi i) htp⟩
      let q : sector (alpha j) :=
        ⟨cylindricalPoint rq w tq,
          cylindrical_mem_sector rq w tq (alpha j) hrq.le (ha j) (hapi j) hq⟩
      let Q := cylindricalPoint rq w T
      have hV : 0 ≤ V := runWidth_nonneg next alpha ha (next i) m
      have hTbeta : beta ≤ T := by dsimp only [T]; linarith [hq.1]
      have htpbeta : tp ≤ beta := htp.2
      have hshort : T - tp < Real.pi := by
        simpa only [runWidth_succ, beta, V, T] using hspanpi
      have hcross : ∃ r s : ℝ, 0 < r ∧
          dist p.val (cylindricalPoint r s beta) +
            dist (cylindricalPoint r s beta) Q = dist p.val Q := by
        by_cases hpwall : tp = beta
        · refine ⟨rp, z, hrp, ?_⟩
          change dist (cylindricalPoint rp z tp) (cylindricalPoint rp z beta) +
            dist (cylindricalPoint rp z beta) Q = dist (cylindricalPoint rp z tp) Q
          simp only [hpwall, dist_self, zero_add]
        by_cases hQwall : T = beta
        · have hVzero : V = 0 := by
            apply le_antisymm
            · dsimp only [T] at hQwall
              linarith [hq.1]
            · exact hV
          have htqzero : tq = 0 := by
            dsimp only [T] at hQwall
            linarith [hq.1]
          have hmzero : m = 0 := by
            by_contra hm
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
            have hVpos : 0 < V := by
              dsimp only [V]
              rw [hk, runWidth_succ]
              exact add_pos_of_pos_of_nonneg (ha (next i))
                (runWidth_nonneg next alpha ha (next (next i)) k)
            exact hVpos.ne' hVzero


          subst m
          subst tq
          refine ⟨rq, w, hrq, ?_⟩
          change dist p.val (cylindricalPoint rq w beta) +
            dist (cylindricalPoint rq w beta) (cylindricalPoint rq w T) =
              dist p.val (cylindricalPoint rq w T)
          simp only [hQwall, dist_self, add_zero]
        · exact strict_wall_crossing rp z tp rq w T beta hrp hrq (ha i) (hapi i)
            (lt_of_le_of_ne htpbeta hpwall)
            (lt_of_le_of_ne hTbeta (Ne.symm hQwall)) hshort
      obtain ⟨r, s, hr, hsplit⟩ := hcross
      let R : G.dom i :=
        ⟨⟨cylindricalPoint r s beta,
          cylindrical_mem_sector r s beta beta hr.le (ha i) (hapi i)
            ⟨(ha i).le, le_rfl⟩⟩,
          by
            change Real.cos beta * lift (cylindricalPoint r s beta) 1 -
              Real.sin beta * lift (cylindricalPoint r s beta) 0 = 0
            rw [cylindrical_wall, sub_self, Real.sin_zero, mul_zero]⟩
      have hrotateR : turn (-beta) (cylindricalPoint r s beta) =
          cylindricalPoint r s 0 := by
        rw [turn_cylindrical, neg_add_cancel]
      have hrotateQ : turn (-beta) Q = cylindricalPoint rq w (V + tq) := by
        dsimp only [Q]
        rw [turn_cylindrical]
        congr 1
        dsimp only [T]
        ring
      have hisoR : (G.iso i R).val =
          (⟨cylindricalPoint r s 0,
            cylindrical_mem_sector r s 0 (alpha (next i)) hr.le
              (ha (next i)) (hapi (next i)) ⟨le_rfl, (ha (next i)).le⟩⟩ :
                sector (alpha (next i))) := by
        apply Subtype.ext
        change turn (-beta) (cylindricalPoint r s beta) = cylindricalPoint r s 0
        exact hrotateR
      have htail0 : 0 ≤ V + tq - 0 := by linarith [hq.1]
      have htailpi : V + tq - 0 < Real.pi := by
        dsimp only [T] at hshort
        linarith
      have htail := ih (i := next i) (rp := r) (z := s) (tp := 0)
        (rq := rq) (w := w) (tq := tq) hr hrq
        ⟨le_rfl, (ha (next i)).le⟩ hq htail0 htailpi
      have htailActual : G.Chain
          ⟨next i, (G.iso i R).val⟩ ⟨j, q⟩
          (ENNReal.ofReal (dist (cylindricalPoint r s 0)
            (cylindricalPoint rq w (V + tq)))) := by
        rw [hisoR]
        simpa only [G, j, q, V] using htail
      have hpaid : G.Chain (⟨i, p⟩ : Sigma (fun k => sector (alpha k)))
          ⟨i, R.val⟩ (ENNReal.ofReal (dist p.val R.val.val)) := by
        simpa only [G, sectorDatum, zero_add, edist_dist, Subtype.dist_eq] using
          D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.move (G := G) (a := ⟨i, p⟩) p R.val
            (D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.nil
              (G := G) (a := ⟨i, p⟩))
      have hforward :=
        D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.forward (G := G) (a := ⟨i, p⟩) i R hpaid
      have happend :=
        D5.S3.Topology.FiniteOrbitChainMetric.Datum.chain_append G hforward htailActual
      have htaildist : dist (cylindricalPoint r s 0)
          (cylindricalPoint rq w (V + tq)) = dist R.val.val Q := by
        change dist (cylindricalPoint r s 0) (cylindricalPoint rq w (V + tq)) =
          dist (cylindricalPoint r s beta) Q
        rw [← hrotateR, ← hrotateQ]
        exact (turn (-beta)).isometry.dist_eq _ _
      rw [htaildist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at happend
      have hsplit' : dist p.val R.val.val + dist R.val.val Q = dist p.val Q := hsplit
      rw [hsplit'] at happend
      simpa only [G, p, q, j, Q, T, V, beta, runWidth_succ,
        Function.iterate_succ_apply] using happend

private theorem folded_angle_eq_of_class (A reference x y : ℝ)
    (h : (x : AddCircle A) = (y : AddCircle A)) :
    foldedAngle A reference x = foldedAngle A reference y := by
  simp only [foldedAngle, AddCircle.coe_sub, h]

private theorem fold_seam {I : Type*} (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (A reference : ℝ) (offset : I → ℝ)
    (hshift : ∀ i, ((offset i + alpha i : ℝ) : AddCircle A) =
      (offset (next i) : AddCircle A)) (i : I)
    (p : (sectorDatum next alpha ha hapi).dom i) :
    fold alpha A reference offset ⟨i, p.val⟩ =
      fold alpha A reference offset
        ⟨next i, ((sectorDatum next alpha ha hapi).iso i p).val⟩ := by
  change cylindricalPoint (radialCoordinate p.val.val) (axialCoordinate p.val.val)
      (foldedAngle A reference (offset i + angularCoordinate p.val.val)) =
    cylindricalPoint (radialCoordinate (turn (-alpha i) p.val.val))
      (axialCoordinate (turn (-alpha i) p.val.val))
      (foldedAngle A reference (offset (next i) + angularCoordinate (turn (-alpha i) p.val.val)))
  rw [turn_radial, turn_axial]
  by_cases hv : transverse p.val.val = 0
  · have hr : radialCoordinate p.val.val = 0 := by
      simp [radialCoordinate, hv]
    simp only [hr, cylindrical_axis]
  · have hu := upper_face_angle (alpha i) (ha i) (hapi i) p hv
    have hl := lower_face_angle (alpha (next i)) (ha (next i)) (hapi (next i))
      ((sectorDatum next alpha ha hapi).iso i p)
    change angularCoordinate (turn (-alpha i) p.val.val) = 0 at hl
    rw [hu, hl, add_zero]
    congr 1
    exact folded_angle_eq_of_class A reference _ _ (hshift i)

private theorem chain_fold_bound {I : Type*} (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (A reference : ℝ) (offset : I → ℝ)
    (hshift : ∀ i, ((offset i + alpha i : ℝ) : AddCircle A) =
      (offset (next i) : AddCircle A))
    (p q : Sigma (fun i => sector (alpha i))) (t : ℝ≥0∞)
    (h : (sectorDatum next alpha ha hapi).Chain p q t) :
    edist (fold alpha A reference offset p) (fold alpha A reference offset q) ≤ t := by
  induction h with
  | nil => simp
  | @move i x y t h ih =>
      have hnon : edist (fold alpha A reference offset ⟨i, x⟩)
          (fold alpha A reference offset ⟨i, y⟩) ≤ edist x y := by
        rw [edist_dist, edist_dist]
        exact ENNReal.ofReal_le_ofReal
          (sector_fold_nonexpanding (alpha i) A reference (offset i) (ha i) (hapi i) x y)
      exact (edist_triangle _ _ _).trans (add_le_add ih hnon)
  | @forward i x t h ih =>
      change edist (fold alpha A reference offset p)
        (fold alpha A reference offset ⟨i,x.val⟩) ≤ t at ih
      change edist (fold alpha A reference offset p)
        (fold alpha A reference offset
          ⟨next i,((sectorDatum next alpha ha hapi).iso i x).val⟩) ≤ t
      rw [← fold_seam next alpha ha hapi A reference offset hshift i x]
      exact ih
  | @backward i x t h ih =>
      change edist (fold alpha A reference offset p)
        (fold alpha A reference offset ⟨next i,x.val⟩) ≤ t at ih
      change edist (fold alpha A reference offset p)
        (fold alpha A reference offset
          ⟨i,(((sectorDatum next alpha ha hapi).iso i).symm x).val⟩) ≤ t
      have heq := fold_seam next alpha ha hapi A reference offset hshift i
        (((sectorDatum next alpha ha hapi).iso i).symm x)
      simp only [IsometryEquiv.apply_symm_apply] at heq
      rw [heq]
      exact ih

private theorem fold_distance_lower {I : Type*} (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (A reference : ℝ) (offset : I → ℝ)
    (hshift : ∀ i, ((offset i + alpha i : ℝ) : AddCircle A) =
      (offset (next i) : AddCircle A))
    (p q : Sigma (fun i => sector (alpha i))) :
    edist (fold alpha A reference offset p) (fold alpha A reference offset q) ≤
      (sectorDatum next alpha ha hapi).distance p q := by
  apply le_iInf
  intro t
  apply le_iInf
  intro h
  exact chain_fold_bound next alpha ha hapi A reference offset hshift p q t h

def offset {n : ℕ} (alpha : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ k ∈ Finset.Iio i, alpha k

def totalAngle {n : ℕ} (alpha : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, alpha k

private def cyclicTag {n : ℕ} (i : Fin (n + 1)) (m : ℕ) : Fin (n + 1) :=
  (finRotate (n + 1))^[m] i

private def cyclicWidth {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, alpha (cyclicTag i k)

private def cyclicWrap {n : ℕ} (i : Fin (n + 1)) : ℕ → ℕ
  | 0 => 0
  | m + 1 => cyclicWrap i m + if cyclicTag i m = Fin.last n then 1 else 0

open Fin.NatCast in
private theorem cyclicTag_add {n : ℕ} (i : Fin (n + 1)) (m : ℕ) :
    cyclicTag i m = i + (m : Fin (n + 1)) := by
  induction m with
  | zero => simp [cyclicTag]
  | succ m ih =>
      simp only [cyclicTag, Function.iterate_succ_apply', finRotate_apply]
      change cyclicTag i m + 1 = _
      rw [ih, Nat.cast_add, Nat.cast_one, add_assoc]

private theorem cyclicTag_difference {n : ℕ} (i j : Fin (n + 1)) :
    cyclicTag i (j - i).val = j := by
  rw [cyclicTag_add]
  simp

private theorem cyclicTag_period {n : ℕ} (i : Fin (n + 1)) :
    cyclicTag i (n + 1) = i := by
  rw [cyclicTag_add, Fin.natCast_self, add_zero]

private theorem cyclic_offset_real {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    offset alpha i + alpha i = offset alpha (finRotate (n + 1) i) +
      (if i = Fin.last n then totalAngle alpha else 0) := by
  classical
  have hsum : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  have hz : offset alpha 0 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have h : k < (0 : Fin (n + 1)) := Finset.mem_Iio.mp hk
    exact False.elim (not_lt_of_ge (Fin.zero_le k) h)
  by_cases hi : i = Fin.last n
  · subst i
    have ht : Finset.Iic (Fin.last n) = (Finset.univ : Finset (Fin (n + 1))) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.le_last k
    rw [if_pos rfl, finRotate_last, hz, zero_add, hsum, ht]
    rfl
  · have hn := coe_finRotate_of_ne_last hi
    have hs : Finset.Iio (finRotate (n + 1) i) = Finset.Iic i := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    rw [if_neg hi, add_zero, hsum]
    simp only [offset, hs]

private theorem cyclicWidth_lift {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (m : ℕ) :
    cyclicWidth alpha i m = offset alpha (cyclicTag i m) - offset alpha i +
      (cyclicWrap i m : ℝ) * totalAngle alpha := by
  classical
  induction m with
  | zero => simp [cyclicWidth, cyclicWrap, cyclicTag]
  | succ m ih =>
      have hs := cyclic_offset_real alpha (cyclicTag i m)
      have ht : cyclicTag i (m + 1) = finRotate (n + 1) (cyclicTag i m) := by
        simp only [cyclicTag, Function.iterate_succ_apply']
      rw [cyclicWidth, Finset.sum_range_succ]
      change cyclicWidth alpha i m + alpha (cyclicTag i m) = _
      rw [ih, cyclicWrap, Nat.cast_add, ht]
      split_ifs at hs ⊢ <;> simp only [Nat.cast_one, Nat.cast_zero] <;> linarith

private theorem cyclicWrap_position {n : ℕ} (i : Fin (n + 1)) (m : ℕ) :
    (cyclicTag i m).val + (n + 1) * cyclicWrap i m = i.val + m := by
  classical
  induction m with
  | zero => simp [cyclicTag, cyclicWrap]
  | succ m ih =>
      have ht : cyclicTag i (m + 1) = finRotate (n + 1) (cyclicTag i m) := by
        simp only [cyclicTag, Function.iterate_succ_apply']
      rw [ht, cyclicWrap, coe_finRotate]
      split_ifs with h
      · have hv : (cyclicTag i m).val = n := congrArg Fin.val h
        simp only [Nat.mul_add, Nat.mul_one] at *
        omega
      · simp only [Nat.add_zero] at *
        omega

private theorem cyclicWidth_difference {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    cyclicWidth alpha i (j - i).val = offset alpha j - offset alpha i +
      (if i ≤ j then 0 else totalAngle alpha) := by
  classical
  have hp := cyclicWrap_position i (j - i).val
  rw [cyclicTag_difference] at hp
  have hd := Fin.intCast_val_sub_eq_sub_add_ite j i
  have hn : 0 < n + 1 := Nat.succ_pos n
  have hw : cyclicWrap i (j - i).val = if i ≤ j then 0 else 1 := by
    split_ifs at hd ⊢ with h
    · apply Nat.eq_of_mul_eq_mul_left hn
      omega
    · apply Nat.eq_of_mul_eq_mul_left hn
      omega
  rw [cyclicWidth_lift, cyclicTag_difference, hw]
  split_ifs <;> simp

private theorem cyclicWidth_period {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : cyclicWidth alpha i (n + 1) = totalAngle alpha := by
  have hp := cyclicWrap_position i (n + 1)
  rw [cyclicTag_period] at hp
  have hw : cyclicWrap i (n + 1) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
    simpa only [Nat.mul_one] using Nat.add_left_cancel hp
  rw [cyclicWidth_lift, cyclicTag_period, hw]
  simp

private theorem offset_end_le {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (i : Fin (n + 1)) :
    offset alpha i + alpha i ≤ totalAngle alpha := by
  classical
  have hs : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  rw [hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => (ha k).le)

private theorem offset_end_le_offset {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) {i j : Fin (n + 1)} (hij : i < j) :
    offset alpha i + alpha i ≤ offset alpha j := by
  classical
  have hs : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  rw [hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Iio.mpr ((Finset.mem_Iic.mp hk).trans_lt hij)
  · intro k _ _
    exact (ha k).le

private def forwardSteps {n : ℕ} (i j : Fin (n + 1)) (tp tq : ℝ) : ℕ :=
  if i = j ∧ tq < tp then n + 1 else (j - i).val

private def forwardSpan {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (tp tq : ℝ) : ℝ :=
  cyclicWidth alpha i (forwardSteps i j tp tq) + tq - tp

private theorem forwardSteps_tag {n : ℕ} (i j : Fin (n + 1)) (tp tq : ℝ) :
    cyclicTag i (forwardSteps i j tp tq) = j := by
  classical
  unfold forwardSteps
  split_ifs with h
  · rw [cyclicTag_period, h.1]
  · exact cyclicTag_difference i j

private theorem forwardSpan_nonneg {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (i j : Fin (n + 1)) (tp tq : ℝ)
    (hp : tp ∈ Icc 0 (alpha i)) (hq : tq ∈ Icc 0 (alpha j)) :
    0 ≤ forwardSpan alpha i j tp tq := by
  classical
  unfold forwardSpan forwardSteps
  split_ifs with h
  · rw [cyclicWidth_period]
    have hb : alpha i ≤ totalAngle alpha :=
      (le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => (ha k).le)).trans
        (offset_end_le alpha ha i)
    linarith [hp.2, hq.1]
  · rw [cyclicWidth_difference]
    by_cases hij : i = j
    · subst j
      simp only [le_refl, if_true, sub_self, zero_add]
      have ht : tp ≤ tq := le_of_not_gt (fun hlt => h ⟨rfl, hlt⟩)
      linarith
    · by_cases hle : i ≤ j
      · rw [if_pos hle]
        have he := offset_end_le_offset alpha ha (lt_of_le_of_ne hle hij)
        linarith [hp.2, hq.1]
      · rw [if_neg hle]
        have he := offset_end_le alpha ha i
        have ho : 0 ≤ offset alpha j := Finset.sum_nonneg (fun k _ => (ha k).le)
        linarith [hp.2, hq.1]

private theorem forwardSpan_pair {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (tp tq : ℝ) :
    (i = j ∧ tp = tq ∧ forwardSpan alpha i j tp tq = 0 ∧
      forwardSpan alpha j i tq tp = 0) ∨
    forwardSpan alpha i j tp tq + forwardSpan alpha j i tq tp = totalAngle alpha := by
  classical
  by_cases hij : i = j
  · subst j
    by_cases ht : tp = tq
    · subst tq
      left
      simp [forwardSpan, forwardSteps, cyclicWidth]
    · right
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · simp only [forwardSpan, forwardSteps, true_and, not_lt_of_ge hlt.le,
          if_false, if_true, hlt, sub_self, Fin.val_zero]
        rw [cyclicWidth_period]
        simp [cyclicWidth]
      · simp only [forwardSpan, forwardSteps, true_and, not_lt_of_ge hgt.le,
          if_false, if_true, hgt, sub_self, Fin.val_zero]
        rw [cyclicWidth_period]
        simp [cyclicWidth]
  · right
    have hji : j ≠ i := Ne.symm hij
    simp only [forwardSpan, forwardSteps, hij, hji, false_and, if_false,
      cyclicWidth_difference]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · rw [if_pos hlt.le, if_neg (not_le.mpr hlt)]
      ring
    · rw [if_neg (not_le.mpr hgt), if_pos hgt.le]
      ring

private theorem forwardSpan_class {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (tp tq : ℝ) :
    ((forwardSpan alpha i j tp tq : ℝ) : AddCircle (totalAngle alpha)) =
      ((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha)) := by
  classical
  unfold forwardSpan forwardSteps
  split_ifs with h
  · rw [cyclicWidth_period, h.1]
    simp only [AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_period, zero_add]
    abel
  · rw [cyclicWidth_difference]
    split_ifs <;> simp only [AddCircle.coe_sub, AddCircle.coe_add,
      AddCircle.coe_period, AddCircle.coe_zero] <;> abel

private theorem shorterSpan_norm {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (i j : Fin (n + 1)) (tp tq : ℝ)
    (hp : tp ∈ Icc 0 (alpha i)) (hq : tq ∈ Icc 0 (alpha j)) :
    min (forwardSpan alpha i j tp tq) (forwardSpan alpha j i tq tp) =
      ‖((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha))‖ := by
  classical
  have hA : 0 < totalAngle alpha := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  have hf := forwardSpan_nonneg alpha ha i j tp tq hp hq
  have hb := forwardSpan_nonneg alpha ha j i tq tp hq hp
  have hclass := forwardSpan_class alpha i j tp tq
  have hback : ((forwardSpan alpha j i tq tp : ℝ) : AddCircle (totalAngle alpha)) =
      -((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha)) := by
    rw [forwardSpan_class]
    simp only [AddCircle.coe_sub, AddCircle.coe_add]
    abel
  rcases forwardSpan_pair alpha i j tp tq with hzero | hsum
  · rw [hzero.2.2.1, hzero.2.2.2, min_self]
    rw [hzero.2.2.1] at hclass
    simpa only [AddCircle.coe_zero, norm_zero] using congrArg norm hclass
  · by_cases hle : forwardSpan alpha i j tp tq ≤ forwardSpan alpha j i tq tp
    · rw [min_eq_left hle, ← hclass]
      have hhalf : |forwardSpan alpha i j tp tq| ≤ |totalAngle alpha| / 2 := by
        rw [abs_of_nonneg hf, abs_of_pos hA]
        linarith
      rw [(AddCircle.norm_coe_eq_abs_iff (totalAngle alpha) hA.ne').mpr hhalf,
        abs_of_nonneg hf]
    · rw [min_eq_right (le_of_not_ge hle), ← norm_neg
        (((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha))),
        ← hback]
      have hhalf : |forwardSpan alpha j i tq tp| ≤ |totalAngle alpha| / 2 := by
        rw [abs_of_nonneg hb, abs_of_pos hA]
        linarith
      rw [(AddCircle.norm_coe_eq_abs_iff (totalAngle alpha) hA.ne').mpr hhalf,
        abs_of_nonneg hb]

private theorem cyclic_offset {n : ℕ} (alpha : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ((offset alpha i + alpha i : ℝ) : AddCircle (totalAngle alpha)) =
      (offset alpha (finRotate (n + 1) i) : AddCircle (totalAngle alpha)) := by
  classical
  have hsum : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  rw [hsum]
  by_cases hi : i = Fin.last n
  · subst i
    have htop : Finset.Iic (Fin.last n) = (Finset.univ : Finset (Fin (n + 1))) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.le_last k
    rw [finRotate_last, htop]
    change ((totalAngle alpha : ℝ) : AddCircle (totalAngle alpha)) =
      (offset alpha 0 : AddCircle (totalAngle alpha))
    have hzero : offset alpha 0 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k < (0 : Fin (n + 1)) := Finset.mem_Iio.mp hk
      exact False.elim (not_lt_of_ge (Fin.zero_le k) hk')
    rw [hzero, AddCircle.coe_zero, AddCircle.coe_period]
  · have hnext := coe_finRotate_of_ne_last hi
    have hsets : Finset.Iio (finRotate (n + 1) i) = Finset.Iic i := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    simp only [offset, hsets]

def cyclicDatum {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi) :
    D5.S3.Topology.FiniteOrbitChainMetric.Datum (Fin (n + 1)) (Fin (n + 1))
      (fun i => sector (alpha i)) :=
  sectorDatum (finRotate (n + 1)) alpha ha hapi

def comparisonLength {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (p q : Sigma (fun i => sector (alpha i))) : ℝ :=
  dist (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val) 0)
    (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val)
      (min Real.pi ‖((offset alpha q.1 + angularCoordinate q.2.val -
        (offset alpha p.1 + angularCoordinate p.2.val) : ℝ) : AddCircle (totalAngle alpha))‖))

private theorem turn_axis (theta z : ℝ) :
    turn theta (cylindricalPoint 0 z 0) = cylindricalPoint 0 z 0 := by
  apply lift_injective
  rw [turn_lift, cylindrical_lift]
  ext k
  fin_cases k <;> simp [cylinderLift]

private theorem axis_mem_sector (alpha z : ℝ) :
    cylindricalPoint 0 z 0 ∈ sector alpha := by
  simp [sector, cylindrical_lift, cylinderLift]

private def axisPoint (alpha z : ℝ) : sector alpha :=
  ⟨cylindricalPoint 0 z 0, axis_mem_sector alpha z⟩

private theorem axis_walk {I : Type*} (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (i : I) (m : ℕ) (z : ℝ) :
    (sectorDatum next alpha ha hapi).Chain
      (⟨i, axisPoint (alpha i) z⟩ : Sigma (fun i => sector (alpha i)))
      ⟨next^[m] i, axisPoint (alpha (next^[m] i)) z⟩ 0 := by
  let G := sectorDatum next alpha ha hapi
  induction m with
  | zero => exact (D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.nil (G := G))
  | succ m ih =>
      let j := next^[m] i
      let x : G.dom j := ⟨axisPoint (alpha j) z, by
        change Real.cos (alpha j) * lift (cylindricalPoint 0 z 0) 1 -
          Real.sin (alpha j) * lift (cylindricalPoint 0 z 0) 0 = 0
        simp [cylindrical_lift, cylinderLift]⟩
      have hx : (G.iso j x).val = axisPoint (alpha (next j)) z := by
        apply Subtype.ext
        exact turn_axis (-alpha j) z
      have h := D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.forward (G := G) j x ih
      rw [hx] at h
      change G.Chain ⟨i, axisPoint (alpha i) z⟩
        ⟨next^[m + 1] i, axisPoint (alpha (next^[m + 1] i)) z⟩ 0
      rw [Function.iterate_succ_apply']
      exact h

private theorem axis_change_tag {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (i j : Fin (n + 1)) (z : ℝ) :
    (cyclicDatum alpha ha hapi).Chain
      (⟨i, axisPoint (alpha i) z⟩ : Sigma (fun i => sector (alpha i)))
      ⟨j, axisPoint (alpha j) z⟩ 0 := by
  have h := axis_walk (finRotate (n + 1)) alpha ha hapi i (j - i).val z
  change (cyclicDatum alpha ha hapi).Chain _
    ⟨cyclicTag i (j - i).val, axisPoint (alpha (cyclicTag i (j - i).val)) z⟩ 0 at h
  rw [cyclicTag_difference] at h
  exact h

private theorem chain_via_axis {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) (z : ℝ) :
    (cyclicDatum alpha ha hapi).Chain p q
      (ENNReal.ofReal (dist p.2.val (cylindricalPoint 0 z 0) +
        dist (cylindricalPoint 0 z 0) q.2.val)) := by
  let G := cyclicDatum alpha ha hapi
  have hfirst : G.Chain p ⟨p.1, axisPoint (alpha p.1) z⟩
      (edist p.2 (axisPoint (alpha p.1) z)) := by
    simpa only [zero_add] using D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.move (G := G) (a := p) p.2 (axisPoint (alpha p.1) z) (D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.nil (G := G))
  have hmid := G.chain_append hfirst (axis_change_tag alpha ha hapi p.1 q.1 z)
  have h := D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.move (G := G) (a := p) (axisPoint (alpha q.1) z) q.2 hmid
  simpa only [add_zero, edist_dist, Subtype.dist_eq, axisPoint,
    ENNReal.ofReal_add dist_nonneg dist_nonneg] using h

private theorem cylindrical_distance_of_cos {rho z theta sigma w phi beta gamma : ℝ}
    (hc : Real.cos (theta - phi) = Real.cos (beta - gamma)) :
    dist (cylindricalPoint rho z theta) (cylindricalPoint sigma w phi) =
      dist (cylindricalPoint rho z beta) (cylindricalPoint sigma w gamma) := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  rw [cylindrical_cosh_distance, cylindrical_cosh_distance, hc]

private theorem cylindrical_axis_distance (rho z theta w : ℝ) :
    dist (cylindricalPoint rho z theta) (cylindricalPoint 0 w 0) =
      dist (cylindricalPoint rho z 0) (cylindricalPoint 0 w 0) := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  simp only [cylindrical_cosh_distance, Real.cosh_zero, Real.sinh_zero, mul_zero,
    zero_mul, sub_zero]

private theorem opposite_axis_split (rho z sigma w : ℝ) (hr : 0 < rho) (hs : 0 < sigma) :
    ∃ a : ℝ,
      dist (cylindricalPoint rho z 0) (cylindricalPoint 0 a 0) +
        dist (cylindricalPoint 0 a 0) (cylindricalPoint sigma w Real.pi) =
      dist (cylindricalPoint rho z 0) (cylindricalPoint sigma w Real.pi) := by
  let p := cylindricalPoint rho z 0
  let q := cylindricalPoint sigma w Real.pi
  have hp : lift p 0 = Real.sinh rho := by simp [p, cylindrical_lift, cylinderLift]
  have hq : lift q 0 = -Real.sinh sigma := by simp [q, cylindrical_lift, cylinderLift]
  have hpy : lift p 1 = 0 := by simp [p, cylindrical_lift, cylinderLift]
  have hqy : lift q 1 = 0 := by simp [q, cylindrical_lift, cylinderLift]
  have hpq : p ≠ q := by
    intro h
    have hx := congrArg (fun r => lift r 0) h
    rw [hp, hq] at hx
    linarith [Real.sinh_pos_iff.mpr hr, Real.sinh_pos_iff.mpr hs]
  obtain ⟨gamma, hiso, h0, h1, hg, hbetween⟩ := hyperbolic_segment p q hpq
  let t0 : Icc (0 : ℝ) (dist p q) := ⟨0, ⟨le_rfl, dist_nonneg⟩⟩
  let t1 : Icc (0 : ℝ) (dist p q) := ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩
  have hc : Continuous (fun t => lift (gamma t) 0) :=
    (continuous_apply 0).comp
      (D5.S3.Geometry.HyperbolicSupportBoundary.lift_continuous.comp hiso.continuous)
  have hx0 : lift (gamma t1) 0 ≤ 0 := by
    rw [h1, hq]
    exact neg_nonpos.mpr (Real.sinh_pos_iff.mpr hs).le
  have hx1 : 0 ≤ lift (gamma t0) 0 := by
    rw [h0, hp]
    exact (Real.sinh_pos_iff.mpr hr).le
  letI : PreconnectedSpace (Icc (0 : ℝ) (dist p q)) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  obtain ⟨t, ht⟩ := intermediate_value_univ t1 t0 hc ⟨hx0, hx1⟩
  have hy : lift (gamma t) 1 = 0 := by
    rw [hg]
    simp [interpolate, hpy, hqy]
  have hv : transverse (gamma t) = 0 := by
    apply Complex.ext <;> simp [transverse, ht, hy]
  have hr0 : radialCoordinate (gamma t) = 0 := by simp [radialCoordinate, hv]
  have he : gamma t = cylindricalPoint 0 (axialCoordinate (gamma t)) 0 := by
    have h := cylindrical_reconstruct (gamma t)
    rw [hr0, cylindrical_axis] at h
    exact h.symm
  refine ⟨axialCoordinate (gamma t), ?_⟩
  have hb : dist p (gamma t) + dist (gamma t) q = dist p q :=
    (show gamma t ∈ {r | dist p r + dist r q = dist p q} from
      hbetween ▸ Set.mem_range_self t)
  rw [← he]
  exact hb

private theorem opposite_attaining_chain {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i)))
    (hp : 0 < radialCoordinate p.2.val) (hq : 0 < radialCoordinate q.2.val) :
    (cyclicDatum alpha ha hapi).Chain p q
      (ENNReal.ofReal (dist
        (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val) 0)
        (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) Real.pi))) := by
  obtain ⟨a, hsplit⟩ := opposite_axis_split
    (radialCoordinate p.2.val) (axialCoordinate p.2.val)
    (radialCoordinate q.2.val) (axialCoordinate q.2.val) hp hq
  have h := chain_via_axis alpha ha hapi p q a
  have hd : dist p.2.val (cylindricalPoint 0 a 0) +
      dist (cylindricalPoint 0 a 0) q.2.val =
      dist (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val) 0)
        (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) Real.pi) := by
    conv_lhs =>
      arg 1
      rw [← cylindrical_reconstruct p.2.val, cylindrical_axis_distance]
    conv_lhs =>
      arg 2
      rw [dist_comm, ← cylindrical_reconstruct q.2.val, cylindrical_axis_distance, dist_comm]
    have hdq : dist (cylindricalPoint 0 a 0)
        (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) Real.pi) =
        dist (cylindricalPoint 0 a 0)
          (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) 0) := by
      rw [dist_comm, cylindrical_axis_distance, dist_comm]
    rw [hdq] at hsplit
    exact hsplit
  simpa only [hd] using h

private theorem comparisonLength_symm {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (p q : Sigma (fun i => sector (alpha i))) :
    comparisonLength alpha p q = comparisonLength alpha q p := by
  have hd : ((offset alpha p.1 + angularCoordinate p.2.val -
      (offset alpha q.1 + angularCoordinate q.2.val) : ℝ) : AddCircle (totalAngle alpha)) =
      -((offset alpha q.1 + angularCoordinate q.2.val -
        (offset alpha p.1 + angularCoordinate p.2.val) : ℝ) : AddCircle (totalAngle alpha)) := by
    simp only [AddCircle.coe_sub, AddCircle.coe_add]
    abel
  unfold comparisonLength
  rw [hd, norm_neg]
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  rw [cylindrical_cosh_distance, cylindrical_cosh_distance]
  have hz : Real.cosh (axialCoordinate p.2.val - axialCoordinate q.2.val) =
      Real.cosh (axialCoordinate q.2.val - axialCoordinate p.2.val) := by
    rw [← Real.cosh_neg, neg_sub]
  rw [hz]
  ring

private theorem axis_endpoint_attaining {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) (hp : radialCoordinate p.2.val = 0) :
    (cyclicDatum alpha ha hapi).Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) := by
  have hpaxis : p.2.val = cylindricalPoint 0 (axialCoordinate p.2.val) 0 := by
    have h := cylindrical_reconstruct p.2.val
    rw [hp, cylindrical_axis] at h
    exact h.symm
  have h := chain_via_axis alpha ha hapi p q (axialCoordinate p.2.val)
  have hd : dist p.2.val (cylindricalPoint 0 (axialCoordinate p.2.val) 0) +
      dist (cylindricalPoint 0 (axialCoordinate p.2.val) 0) q.2.val =
      comparisonLength alpha p q := by
    have h0 : dist p.2.val (cylindricalPoint 0 (axialCoordinate p.2.val) 0) = 0 :=
      dist_eq_zero.mpr hpaxis
    rw [h0, zero_add]
    conv_lhs =>
      arg 2
      rw [← cylindrical_reconstruct q.2.val]
    unfold comparisonLength
    rw [hp]
    apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
    rw [cylindrical_cosh_distance, cylindrical_cosh_distance]
    simp only [Real.sinh_zero, zero_mul, sub_zero]
  simpa only [hd] using h

/-- The capped scalar angular separation gives a lower bound for the literal
original cost infimum on numbered actual hyperbolic sectors. -/
private theorem comparison_lower {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) :
    ENNReal.ofReal (comparisonLength alpha p q) ≤ (cyclicDatum alpha ha hapi).distance p q := by
  have h := fold_distance_lower (finRotate (n + 1)) alpha ha hapi (totalAngle alpha)
    (offset alpha p.1 + angularCoordinate p.2.val) (offset alpha) (cyclic_offset alpha) p q
  simpa only [fold, foldedAngle, sub_self, AddCircle.coe_zero, norm_zero,
    min_eq_right Real.pi_pos.le, edist_dist, comparisonLength, cyclicDatum] using h

private theorem short_forward_attaining {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i)))
    (hp : 0 < radialCoordinate p.2.val) (hq : 0 < radialCoordinate q.2.val)
    (hle : forwardSpan alpha p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val) ≤
      forwardSpan alpha q.1 p.1 (angularCoordinate q.2.val) (angularCoordinate p.2.val))
    (hshort : forwardSpan alpha p.1 q.1 (angularCoordinate p.2.val)
      (angularCoordinate q.2.val) < Real.pi) :
    (cyclicDatum alpha ha hapi).Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) := by
  let m := forwardSteps p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
  have htag := forwardSteps_tag p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
  have hwp : runWidth (finRotate (n + 1)) alpha p.1 m = cyclicWidth alpha p.1 m := rfl
  have hqangle : angularCoordinate q.2.val ∈
      Icc 0 (alpha ((finRotate (n + 1))^[m] p.1)) := by
    change angularCoordinate q.2.val ∈ Icc 0 (alpha (cyclicTag p.1 m))
    rw [htag]
    exact sector_angle (alpha q.1) (ha q.1) q.2
  have hspan := forwardSpan_nonneg alpha ha p.1 q.1
    (angularCoordinate p.2.val) (angularCoordinate q.2.val)
    (sector_angle (alpha p.1) (ha p.1) p.2) (sector_angle (alpha q.1) (ha q.1) q.2)
  have h := short_angle_forward_run (finRotate (n + 1)) alpha ha hapi m p.1
    (radialCoordinate p.2.val) (axialCoordinate p.2.val) (angularCoordinate p.2.val)
    (radialCoordinate q.2.val) (axialCoordinate q.2.val) (angularCoordinate q.2.val)
    hp hq (sector_angle (alpha p.1) (ha p.1) p.2) hqangle
    (by simpa only [hwp, forwardSpan, m] using hspan)
    (by simpa only [hwp, forwardSpan, m] using hshort)
  have hd : dist
      (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val)
        (angularCoordinate p.2.val))
      (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val)
        (runWidth (finRotate (n + 1)) alpha p.1 m + angularCoordinate q.2.val)) =
      comparisonLength alpha p q := by
    have hn := shorterSpan_norm alpha ha p.1 q.1
      (angularCoordinate p.2.val) (angularCoordinate q.2.val)
      (sector_angle (alpha p.1) (ha p.1) p.2) (sector_angle (alpha q.1) (ha q.1) q.2)
    rw [min_eq_left hle] at hn
    unfold comparisonLength
    rw [← hn, min_eq_right hshort.le]
    apply cylindrical_distance_of_cos
    rw [hwp]
    congr 1
    change angularCoordinate p.2.val -
      (cyclicWidth alpha p.1 m + angularCoordinate q.2.val) =
      0 - (cyclicWidth alpha p.1 m + angularCoordinate q.2.val - angularCoordinate p.2.val)
    ring
  rw [hd] at h
  change (cyclicDatum alpha ha hapi).Chain
    ⟨p.1, _⟩ ⟨cyclicTag p.1 m, _⟩ _ at h
  rw [show cyclicTag p.1 m = q.1 from htag] at h
  simpa only [cylindrical_reconstruct] using h

/-- Every pair of actual numbered cyclic-sector representatives has an original
finite chain attaining the capped angular distance, which equals the original
cost infimum. -/
theorem cyclic_sector_metric {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) :
    (cyclicDatum alpha ha hapi).Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) ∧
      (cyclicDatum alpha ha hapi).distance p q = ENNReal.ofReal (comparisonLength alpha p q) := by
  let G := cyclicDatum alpha ha hapi
  have hattain : G.Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) := by
    have hrp : 0 ≤ radialCoordinate p.2.val :=
      Real.arsinh_nonneg_iff.mpr (norm_nonneg _)
    have hrq : 0 ≤ radialCoordinate q.2.val :=
      Real.arsinh_nonneg_iff.mpr (norm_nonneg _)
    rcases eq_or_lt_of_le hrp with hp | hp
    · exact axis_endpoint_attaining alpha ha hapi p q hp.symm
    rcases eq_or_lt_of_le hrq with hq | hq
    · have h := G.chain_reverse (axis_endpoint_attaining alpha ha hapi q p hq.symm)
      simpa only [comparisonLength_symm alpha q p] using h
    let f := forwardSpan alpha p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
    let b := forwardSpan alpha q.1 p.1 (angularCoordinate q.2.val) (angularCoordinate p.2.val)
    have hn : min f b = ‖((offset alpha q.1 + angularCoordinate q.2.val -
        (offset alpha p.1 + angularCoordinate p.2.val) : ℝ) : AddCircle (totalAngle alpha))‖ :=
      shorterSpan_norm alpha ha p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
        (sector_angle (alpha p.1) (ha p.1) p.2) (sector_angle (alpha q.1) (ha q.1) q.2)
    by_cases hcap : Real.pi ≤ min f b
    · have h := opposite_attaining_chain alpha ha hapi p q hp hq
      change G.Chain p q (ENNReal.ofReal (comparisonLength alpha p q))
      simpa only [comparisonLength, min_eq_left (hn ▸ hcap)] using h
    · have hmin : min f b < Real.pi := lt_of_not_ge hcap
      by_cases hle : f ≤ b
      · exact short_forward_attaining alpha ha hapi p q hp hq hle
          (by simpa only [min_eq_left hle] using hmin)
      · have hle' := le_of_not_ge hle
        have h := G.chain_reverse (short_forward_attaining alpha ha hapi q p hq hp hle'
          (by simpa only [min_eq_right hle'] using hmin))
        simpa only [comparisonLength_symm alpha q p] using h
  exact ⟨hattain, le_antisymm
    (iInf₂_le (ENNReal.ofReal (comparisonLength alpha p q)) hattain)
    (comparison_lower alpha ha hapi p q)⟩

end D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric
