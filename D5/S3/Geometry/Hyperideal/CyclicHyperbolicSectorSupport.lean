/- GID: D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorSupport
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CyclicHyperbolicSectorSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.AddCircle, mathlib/module/Mathlib.Analysis.Complex.Isometry]
   utility: none
   digest: Coordinate and seam support for cyclic hyperbolic sector metrics. -/

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

def cylinderLift (rho z theta : ℝ) : Fin 4 → ℝ :=
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

theorem cylindrical_lift (rho z theta : ℝ) :
    lift (cylindricalPoint rho z theta) = cylinderLift rho z theta :=
  lift_of_coordinates _ _ (cylinder_unit rho z theta)
    (by change 0 < Real.cosh rho * Real.cosh z; positivity) rfl

theorem cylindrical_cosh_distance (rho z theta sigma w phi : ℝ) :
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

theorem cylindrical_axis (z theta : ℝ) :
    cylindricalPoint 0 z theta = cylindricalPoint 0 z 0 := by
  apply lift_injective
  simp [cylindrical_lift, cylinderLift]

def transverse (p : HyperbolicThreeSpace) : ℂ :=
  ⟨lift p 0, lift p 1⟩

def radialCoordinate (p : HyperbolicThreeSpace) : ℝ :=
  Real.arsinh ‖transverse p‖

def axialCoordinate (p : HyperbolicThreeSpace) : ℝ :=
  Real.arsinh (lift p 2 / Real.cosh (radialCoordinate p))

def angularCoordinate (p : HyperbolicThreeSpace) : ℝ :=
  (transverse p).arg

theorem cylindrical_reconstruct (p : HyperbolicThreeSpace) :
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

def foldedAngle (A reference theta : ℝ) : ℝ :=
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

def turn (theta : ℝ) : HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace :=
  horizontalIso (_root_.rotation (Circle.exp theta))

theorem turn_lift (theta : ℝ) (p : HyperbolicThreeSpace) :
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

theorem sector_angle (alpha : ℝ) (ha : 0 < alpha)
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

def sectorDatum {I : Type*} (next : I → I) (alpha : I → ℝ)
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

def fold {I : Type*} (alpha : I → ℝ) (A reference : ℝ) (offset : I → ℝ)
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

def runWidth {I : Type*} (next : I → I) (alpha : I → ℝ)
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

theorem cylindrical_mem_sector (rho z theta beta : ℝ)
    (hr : 0 ≤ rho) (hbpi : beta < Real.pi)
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
  obtain ⟨gamma, _, _, _, hgamma, hbetween⟩ :=
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


theorem short_angle_forward_run {I : Type*}
    (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (m : ℕ) (i : I) (rp z tp rq w tq : ℝ)
    (hrp : 0 < rp) (hrq : 0 < rq)
    (htp : tp ∈ Icc 0 (alpha i))
    (htq : tq ∈ Icc 0 (alpha (next^[m] i)))
    (hspanpi : runWidth next alpha i m + tq - tp < Real.pi) :
    (sectorDatum next alpha ha hapi).Chain
      ⟨i, ⟨cylindricalPoint rp z tp,
        cylindrical_mem_sector rp z tp (alpha i) hrp.le (hapi i) htp⟩⟩
      ⟨next^[m] i, ⟨cylindricalPoint rq w tq,
        cylindrical_mem_sector rq w tq (alpha (next^[m] i))
          hrq.le (hapi _) htq⟩⟩
      (ENNReal.ofReal (dist (cylindricalPoint rp z tp)
        (cylindricalPoint rq w (runWidth next alpha i m + tq)))) := by
  induction m generalizing i rp z tp rq w tq with
  | zero =>
      let p : sector (alpha i) :=
        ⟨cylindricalPoint rp z tp,
          cylindrical_mem_sector rp z tp (alpha i) hrp.le (hapi i) htp⟩
      have hq : tq ∈ Icc 0 (alpha i) := by
        simpa only [Function.iterate_zero_apply] using htq
      let q : sector (alpha i) :=
        ⟨cylindricalPoint rq w tq,
          cylindrical_mem_sector rq w tq (alpha i) hrq.le (hapi i) hq⟩
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
          cylindrical_mem_sector rp z tp (alpha i) hrp.le (hapi i) htp⟩
      let q : sector (alpha j) :=
        ⟨cylindricalPoint rq w tq,
          cylindrical_mem_sector rq w tq (alpha j) hrq.le (hapi j) hq⟩
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
          cylindrical_mem_sector r s beta beta hr.le (hapi i)
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
              (hapi (next i)) ⟨le_rfl, (ha (next i)).le⟩⟩ :
                sector (alpha (next i))) := by
        apply Subtype.ext
        change turn (-beta) (cylindricalPoint r s beta) = cylindricalPoint r s 0
        exact hrotateR
      have htailpi : V + tq - 0 < Real.pi := by
        dsimp only [T] at hshort
        linarith
      have htail := ih (i := next i) (rp := r) (z := s) (tp := 0)
        (rq := rq) (w := w) (tq := tq) hr hrq
        ⟨le_rfl, (ha (next i)).le⟩ hq htailpi
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

theorem fold_distance_lower {I : Type*} (next : I → I) (alpha : I → ℝ)
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


end D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric
