import D5.S3.Geometry.HyperbolicUpperHalfSpace
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real

/-! The Euclidean AdS₃ upper half-space and its cyclic loxodromic quotient and conformal compactification. -/

noncomputable section
set_option autoImplicit false

open Function Metric Set Topology

namespace D5.S3.Geometry.AdS3LoxodromicQuotient

abbrev UpperHalfSpace := HyperbolicUpperHalfSpace.UpperHalfSpace ℂ

/-- The ordinary complex coordinate and the positive real height. -/
def coordinates (x : UpperHalfSpace) : ℂ × ℝ := WithLp.ofLp x.val

private theorem height_pos (x : UpperHalfSpace) : 0 < (coordinates x).2 := x.property

private theorem continuous_coordinates : Continuous coordinates :=
  (WithLp.prod_continuous_ofLp 2 ℂ ℝ).comp continuous_subtype_val

/-- The hyperbolic metric evaluated twice on a tangent vector in the upper half-space chart. -/
def hyperbolicQuadratic (x : UpperHalfSpace) (v : ℂ × ℝ) : ℝ :=
  (‖v.1‖ ^ 2 + v.2 ^ 2) / (coordinates x).2 ^ 2

structure Loxodromic where
  rho : ℝ
  theta : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1

def phase (s : ℝ) : ℂ := Complex.exp ((s : ℂ) * Complex.I)

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_zero : phase 0 = 1 := by simp [phase]

private theorem phase_neg_mul (s : ℝ) : phase (-s) * phase s = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

private theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I s

private theorem continuous_phase : Continuous phase :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

namespace Loxodromic

variable (g : Loxodromic)

def multiplier (n : ℤ) : ℂ := ((g.rho ^ n : ℝ) : ℂ) * phase ((n : ℝ) * g.theta)

private theorem multiplier_add (m n : ℤ) :
    g.multiplier (m + n) = g.multiplier m * g.multiplier n := by
  simp only [multiplier, zpow_add₀ g.rho_pos.ne' m n, Complex.ofReal_mul, Int.cast_add,
    add_mul, phase_add]
  ring

/-- The action extends to a real-linear map on the ambient coordinate space. -/
def tangentMap (n : ℤ) : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) :=
  ((ContinuousLinearMap.mul ℝ ℂ) (g.multiplier n)).prodMap
    ((ContinuousLinearMap.mul ℝ ℝ) (g.rho ^ n))

theorem tangentMap_apply (n : ℤ) (v : ℂ × ℝ) :
    g.tangentMap n v = (g.multiplier n * v.1, g.rho ^ n * v.2) :=
  rfl

def act (n : ℤ) (x : UpperHalfSpace) : UpperHalfSpace :=
  ⟨WithLp.toLp 2 (g.tangentMap n (coordinates x)), mul_pos (zpow_pos g.rho_pos n) (height_pos x)⟩

theorem coordinates_act (n : ℤ) (x : UpperHalfSpace) :
    coordinates (g.act n x) =
      (g.multiplier n * (coordinates x).1, g.rho ^ n * (coordinates x).2) :=
  rfl

theorem act_zero (x : UpperHalfSpace) : g.act 0 x = x := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change coordinates (g.act 0 x) = coordinates x
  simp [coordinates_act, multiplier, phase_zero]

theorem act_add (m n : ℤ) (x : UpperHalfSpace) : g.act (m + n) x = g.act m (g.act n x) := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change coordinates (g.act (m + n) x) = coordinates (g.act m (g.act n x))
  simp only [coordinates_act, g.multiplier_add, zpow_add₀ g.rho_pos.ne' m n, mul_assoc]

@[instance_reducible]
def integerAction : AddAction ℤ UpperHalfSpace where
  vadd := g.act
  zero_vadd := g.act_zero
  add_vadd := g.act_add

/-- The Fréchet derivative of the coordinate formula of the action. -/
theorem hasFDerivAt_act (n : ℤ) (p : ℂ × ℝ) :
    HasFDerivAt (fun x : ℂ × ℝ => (g.multiplier n * x.1, g.rho ^ n * x.2))
      (g.tangentMap n) p :=
  (g.tangentMap n).hasFDerivAt

theorem hyperbolicQuadratic_act (n : ℤ) (x : UpperHalfSpace) (v : ℂ × ℝ) :
    hyperbolicQuadratic (g.act n x) (g.tangentMap n v) = hyperbolicQuadratic x v := by
  have hscale : 0 < g.rho ^ n := zpow_pos g.rho_pos n
  have hz : ‖g.multiplier n * v.1‖ = g.rho ^ n * ‖v.1‖ := by
    simp only [multiplier, norm_mul, Complex.norm_of_nonneg hscale.le, norm_phase, mul_one]
  simp only [hyperbolicQuadratic, g.coordinates_act, tangentMap_apply, hz]
  apply (div_eq_div_iff (pow_ne_zero 2 (mul_pos hscale (height_pos x)).ne')
    (pow_ne_zero 2 (height_pos x).ne')).2
  ring

theorem hyperbolicQuadratic_fderiv_act (n : ℤ) (x : UpperHalfSpace) (v : ℂ × ℝ) :
    hyperbolicQuadratic (g.act n x)
      (fderiv ℝ (fun p : ℂ × ℝ => (g.multiplier n * p.1, g.rho ^ n * p.2))
        (coordinates x) v) = hyperbolicQuadratic x v := by
  rw [(g.hasFDerivAt_act n (coordinates x)).fderiv]
  exact g.hyperbolicQuadratic_act n x v

def time (x : UpperHalfSpace) : ℝ := Real.log (coordinates x).2 / Real.log g.rho

private theorem log_rho_ne_zero : Real.log g.rho ≠ 0 :=
  (Real.log_neg g.rho_pos g.rho_lt_one).ne

private theorem exp_time (x : UpperHalfSpace) :
    Real.exp (g.time x * Real.log g.rho) = (coordinates x).2 := by
  rw [time, div_mul_cancel₀ _ g.log_rho_ne_zero, Real.exp_log (height_pos x)]

private def toCylinder (x : UpperHalfSpace) : ℂ × ℝ :=
  (phase (-g.theta * g.time x) * (coordinates x).1 / ((coordinates x).2 : ℂ), g.time x)

private def fromCylinder (p : ℂ × ℝ) : UpperHalfSpace :=
  let r := Real.exp (p.2 * Real.log g.rho)
  ⟨WithLp.toLp 2 ((r : ℂ) * phase (g.theta * p.2) * p.1, r), Real.exp_pos _⟩

private theorem time_fromCylinder (p : ℂ × ℝ) : g.time (g.fromCylinder p) = p.2 := by
  change Real.log (Real.exp (p.2 * Real.log g.rho)) / Real.log g.rho = p.2
  rw [Real.log_exp, mul_div_cancel_right₀ _ g.log_rho_ne_zero]

private theorem fromCylinder_toCylinder (x : UpperHalfSpace) :
    g.fromCylinder (g.toCylinder x) = x := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change ((↑(Real.exp (g.time x * Real.log g.rho)) : ℂ) *
      phase (g.theta * g.time x) *
      (phase (-g.theta * g.time x) * (coordinates x).1 / ((coordinates x).2 : ℂ)),
    Real.exp (g.time x * Real.log g.rho)) = coordinates x
  rw [g.exp_time x]
  refine Prod.ext ?_ rfl
  have hr : ((coordinates x).2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (height_pos x).ne'
  have hp : phase (g.theta * g.time x) * phase (-g.theta * g.time x) = 1 := by
    rw [neg_mul, mul_comm, phase_neg_mul]
  calc
    _ = (phase (g.theta * g.time x) * phase (-g.theta * g.time x)) *
        (((coordinates x).2 : ℂ) * (coordinates x).1 / ((coordinates x).2 : ℂ)) := by
          simp only [div_eq_mul_inv]
          ring
    _ = (coordinates x).1 := by rw [hp, one_mul, mul_div_cancel_left₀ _ hr]

private theorem toCylinder_fromCylinder (p : ℂ × ℝ) :
    g.toCylinder (g.fromCylinder p) = p := by
  refine Prod.ext ?_ (g.time_fromCylinder p)
  change phase (-g.theta * g.time (g.fromCylinder p)) *
      ((Real.exp (p.2 * Real.log g.rho) : ℂ) * phase (g.theta * p.2) * p.1) /
      (Real.exp (p.2 * Real.log g.rho) : ℂ) = p.1
  rw [g.time_fromCylinder p]
  have hr : (Real.exp (p.2 * Real.log g.rho) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hp : phase (-g.theta * p.2) * phase (g.theta * p.2) = 1 := by
    rw [neg_mul, phase_neg_mul]
  calc
    _ = (Real.exp (p.2 * Real.log g.rho) : ℂ) *
        ((phase (-g.theta * p.2) * phase (g.theta * p.2)) * p.1) /
        (Real.exp (p.2 * Real.log g.rho) : ℂ) := by ring
    _ = p.1 := by rw [hp, one_mul, mul_div_cancel_left₀ _ hr]

/-- Logarithmic height and the rescaled, untwisted complex coordinate. -/
def coverHomeomorph : UpperHalfSpace ≃ₜ ℂ × ℝ where
  toFun := g.toCylinder
  invFun := g.fromCylinder
  left_inv := g.fromCylinder_toCylinder
  right_inv := g.toCylinder_fromCylinder
  continuous_toFun := by
    have hr : Continuous (fun x : UpperHalfSpace => (coordinates x).2) :=
      continuous_snd.comp continuous_coordinates
    have hlog : Continuous (fun x : UpperHalfSpace => Real.log (coordinates x).2) :=
      continuous_iff_continuousAt.2 fun x =>
        (Real.continuousAt_log (height_pos x).ne').comp (f := fun y => (coordinates y).2) hr.continuousAt
    have ht : Continuous g.time := hlog.div_const _
    exact (((continuous_phase.comp (continuous_const.mul ht)).mul
      (continuous_fst.comp continuous_coordinates)).div
      (Complex.continuous_ofReal.comp hr)
      (fun x => Complex.ofReal_ne_zero.mpr (height_pos x).ne')).prodMk ht
  continuous_invFun := by
    have hr : Continuous (fun p : ℂ × ℝ => Real.exp (p.2 * Real.log g.rho)) :=
      Real.continuous_exp.comp (continuous_snd.mul continuous_const)
    have hz : Continuous (fun p : ℂ × ℝ =>
        (Real.exp (p.2 * Real.log g.rho) : ℂ) * phase (g.theta * p.2) * p.1) :=
      ((Complex.continuous_ofReal.comp hr).mul
        (continuous_phase.comp (continuous_const.mul continuous_snd))).mul continuous_fst
    exact ((WithLp.prod_continuous_toLp 2 ℂ ℝ).comp (hz.prodMk hr)).subtype_mk _

theorem coverHomeomorph_apply (x : UpperHalfSpace) :
    g.coverHomeomorph x =
      (phase (-g.theta * g.time x) * (coordinates x).1 / ((coordinates x).2 : ℂ), g.time x) :=
  rfl

theorem coordinates_coverHomeomorph_symm (p : ℂ × ℝ) :
    coordinates (g.coverHomeomorph.symm p) =
      ((Real.exp (p.2 * Real.log g.rho) : ℂ) * phase (g.theta * p.2) * p.1,
        Real.exp (p.2 * Real.log g.rho)) :=
  rfl

private theorem time_act (n : ℤ) (x : UpperHalfSpace) :
    g.time (g.act n x) = g.time x + (n : ℝ) := by
  simp only [time, g.coordinates_act]
  rw [Real.log_mul (zpow_pos g.rho_pos n).ne' (height_pos x).ne', Real.log_zpow,
    add_div, mul_div_assoc, div_self g.log_rho_ne_zero, mul_one]
  exact add_comm _ _

/-- In these coordinates the actual action fixes the first coordinate and translates height. -/
theorem coverHomeomorph_act (n : ℤ) (x : UpperHalfSpace) :
    g.coverHomeomorph (g.act n x) = ((g.coverHomeomorph x).1, (g.coverHomeomorph x).2 + (n : ℝ)) := by
  refine Prod.ext ?_ (g.time_act n x)
  have hp : phase (-g.theta * (g.time x + (n : ℝ))) * phase ((n : ℝ) * g.theta) =
      phase (-g.theta * g.time x) := by
    rw [← phase_add]
    congr 1
    ring
  have hr : ((g.rho ^ n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zpow_pos g.rho_pos n).ne'
  simp only [g.coverHomeomorph_apply, g.time_act, g.coordinates_act, multiplier, Complex.ofReal_mul]
  calc
    _ = ((g.rho ^ n : ℝ) : ℂ) *
        ((phase (-g.theta * (g.time x + (n : ℝ))) * phase ((n : ℝ) * g.theta)) *
          (coordinates x).1) / (((g.rho ^ n : ℝ) : ℂ) * ((coordinates x).2 : ℂ)) := by ring
    _ = _ := by rw [hp, mul_div_mul_left _ _ hr]

def orbitSetoid : Setoid UpperHalfSpace :=
  letI := g.integerAction
  AddAction.orbitRel ℤ UpperHalfSpace

theorem orbitSetoid_iff (x y : UpperHalfSpace) :
    g.orbitSetoid x y ↔ ∃ n : ℤ, g.act n y = x :=
  Iff.rfl

abbrev OrbitQuotient := Quotient g.orbitSetoid

private def circleProjection : ℂ × ℝ → ℂ × AddCircle (1 : ℝ) :=
  Prod.map id ((↑) : ℝ → AddCircle (1 : ℝ))

private theorem circle_eq_iff (s t : ℝ) :
    (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) ↔ ∃ n : ℤ, s = t + (n : ℝ) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [zsmul_one] at hn
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [zsmul_one]
    linarith

def orbitCoordinates : UpperHalfSpace → ℂ × AddCircle (1 : ℝ) :=
  circleProjection ∘ g.coverHomeomorph

theorem orbitCoordinates_fiber_iff (x y : UpperHalfSpace) :
    g.orbitCoordinates x = g.orbitCoordinates y ↔ ∃ n : ℤ, g.act n y = x := by
  constructor
  · intro h
    have hu : (g.coverHomeomorph x).1 = (g.coverHomeomorph y).1 :=
      congrArg (Prod.fst : ℂ × AddCircle (1 : ℝ) → ℂ) h
    have ht : ((g.coverHomeomorph x).2 : AddCircle (1 : ℝ)) =
        ((g.coverHomeomorph y).2 : AddCircle (1 : ℝ)) := congrArg Prod.snd h
    obtain ⟨n, hn⟩ := (circle_eq_iff _ _).mp ht
    refine ⟨n, g.coverHomeomorph.injective ?_⟩
    rw [g.coverHomeomorph_act]
    exact Prod.ext hu.symm hn.symm
  · rintro ⟨n, rfl⟩
    change circleProjection (g.coverHomeomorph (g.act n y)) = circleProjection (g.coverHomeomorph y)
    rw [g.coverHomeomorph_act]
    exact Prod.ext rfl ((circle_eq_iff _ _).mpr ⟨n, rfl⟩)

private def quotientCoordinates : g.OrbitQuotient → ℂ × AddCircle (1 : ℝ) :=
  Quotient.lift g.orbitCoordinates fun x y h =>
    (g.orbitCoordinates_fiber_iff x y).2 ((g.orbitSetoid_iff x y).1 h)

/-- The geometric orbit quotient with its quotient topology. -/
def orbitHomeomorph : g.OrbitQuotient ≃ₜ ℂ × AddCircle (1 : ℝ) := by
  have hcircle : IsOpenQuotientMap circleProjection :=
    IsOpenQuotientMap.id.prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
  have hcoords : IsOpenQuotientMap g.orbitCoordinates :=
    hcircle.comp g.coverHomeomorph.isOpenQuotientMap
  let q := Quotient.mk g.orbitSetoid
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  have hcomp : g.quotientCoordinates ∘ q = g.orbitCoordinates := rfl
  have hcont : Continuous g.quotientCoordinates :=
    hq.continuous_iff.mpr (by rw [hcomp]; exact hcoords.continuous)
  have hopen : IsOpenMap g.quotientCoordinates :=
    IsOpenMap.of_comp hq.continuous hq.surjective (by rw [hcomp]; exact hcoords.isOpenMap)
  have hinj : Injective g.quotientCoordinates := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y hxy
    exact Quotient.sound ((g.orbitSetoid_iff x y).2 ((g.orbitCoordinates_fiber_iff x y).1 hxy))
  have hsurj : Surjective g.quotientCoordinates := by
    intro p
    obtain ⟨x, hx⟩ := hcoords.surjective p
    exact ⟨q x, hx⟩
  exact (Equiv.ofBijective g.quotientCoordinates ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    hcont hopen

theorem orbitHomeomorph_mk (x : UpperHalfSpace) :
    g.orbitHomeomorph (Quotient.mk g.orbitSetoid x) =
      ((g.coverHomeomorph x).1, ((g.coverHomeomorph x).2 : AddCircle (1 : ℝ))) :=
  rfl

/-- The loxodromic parameters of a point of the complex upper half-plane. -/
def ofTau (τ : ℂ) (hτ : 0 < τ.im) : Loxodromic where
  rho := Real.exp (-(2 * Real.pi * τ.im))
  theta := 2 * Real.pi * τ.re
  rho_pos := Real.exp_pos _
  rho_lt_one := Real.exp_lt_one_iff.mpr
    (neg_neg_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hτ))

theorem ofTau_multiplier (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ) :
    (ofTau τ hτ).multiplier n = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) ^ n := by
  have hbase : (Real.exp (-(2 * Real.pi * τ.im)) : ℂ) * phase (2 * Real.pi * τ.re) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) := by
    rw [Complex.ofReal_exp, phase, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
    calc
      _ = 2 * (Real.pi : ℂ) * Complex.I * (τ.re : ℂ) +
          2 * (Real.pi : ℂ) * (τ.im : ℂ) * (Complex.I * Complex.I) := by
        rw [Complex.I_mul_I]
        ring
      _ = 2 * (Real.pi : ℂ) * Complex.I * ((τ.re : ℂ) + (τ.im : ℂ) * Complex.I) := by ring
      _ = _ := congrArg (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.I * z) (Complex.re_add_im τ)
  rw [← hbase, mul_zpow, multiplier, Complex.ofReal_zpow]
  change (Real.exp (-(2 * Real.pi * τ.im)) : ℂ) ^ n *
      phase ((n : ℝ) * (2 * Real.pi * τ.re)) =
    _ * phase (2 * Real.pi * τ.re) ^ n
  congr 1
  simp only [phase, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc, Complex.exp_int_mul]

end Loxodromic

/-- The upper half-space together with its finite boundary, with the origin removed. -/
abbrev CompactifiedCover := {p : ℂ × ℝ // 0 ≤ p.2 ∧ p ≠ 0}

abbrev ClosedDisk : Type := ↥(Metric.closedBall (0 : ℂ) 1)

private def radiusSq (p : ℂ × ℝ) : ℝ := ‖p.1‖ ^ 2 + p.2 ^ 2

private theorem radiusSq_pos {p : ℂ × ℝ} (hp : p ≠ 0) : 0 < radiusSq p := by
  rcases p with ⟨z, r⟩
  change 0 < ‖z‖ ^ 2 + r ^ 2
  by_contra! h
  have hz : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z‖, sq_nonneg r]
  have hr : r ^ 2 = 0 := by nlinarith [sq_nonneg ‖z‖, sq_nonneg r]
  exact hp (Prod.ext (norm_eq_zero.mp (sq_eq_zero_iff.mp hz)) (sq_eq_zero_iff.mp hr))

/-- The Euclidean distance to the omitted origin. -/
def radius (x : CompactifiedCover) : ℝ := Real.sqrt (radiusSq x.val)

private theorem radius_pos (x : CompactifiedCover) : 0 < radius x :=
  Real.sqrt_pos.mpr (radiusSq_pos x.property.2)

private theorem radius_sq (x : CompactifiedCover) : radius x ^ 2 = radiusSq x.val :=
  Real.sq_sqrt (radiusSq_pos x.property.2).le

theorem continuous_radius : Continuous radius :=
  (((continuous_fst.comp continuous_subtype_val).norm.pow 2).add
    ((continuous_snd.comp continuous_subtype_val).pow 2)).sqrt

/-- The scale-invariant boundary defining function, given by height divided by radius. -/
def boundaryFactor (x : CompactifiedCover) : ℝ := x.val.2 / radius x

theorem continuous_boundaryFactor : Continuous boundaryFactor :=
  (continuous_snd.comp continuous_subtype_val).div continuous_radius
    (fun x => (radius_pos x).ne')

theorem boundaryFactor_nonneg (x : CompactifiedCover) : 0 ≤ boundaryFactor x :=
  div_nonneg x.property.1 (radius_pos x).le

theorem boundaryFactor_eq_zero_iff (x : CompactifiedCover) :
    boundaryFactor x = 0 ↔ x.val.2 = 0 := by
  simp [boundaryFactor, (radius_pos x).ne']

/-- The conformally rescaled tangent quadratic form on the compactified cover. -/
def compactifiedQuadratic (x : CompactifiedCover) (v : ℂ × ℝ) : ℝ :=
  radiusSq v / radius x ^ 2

theorem continuous_compactifiedQuadratic :
    Continuous (fun p : CompactifiedCover × (ℂ × ℝ) => compactifiedQuadratic p.1 p.2) := by
  have hv : Continuous (fun v : ℂ × ℝ => radiusSq v) :=
    (continuous_fst.norm.pow 2).add (continuous_snd.pow 2)
  exact (hv.comp continuous_snd).div ((continuous_radius.comp continuous_fst).pow 2)
    (fun p => pow_ne_zero 2 (radius_pos p.1).ne')

theorem compactifiedQuadratic_pos (x : CompactifiedCover) (v : ℂ × ℝ) (hv : v ≠ 0) :
    0 < compactifiedQuadratic x v :=
  div_pos (radiusSq_pos hv) (pow_pos (radius_pos x) 2)

/-- The original upper half-space in the compactified cover. -/
def interiorPoint (x : UpperHalfSpace) : CompactifiedCover :=
  ⟨coordinates x, (height_pos x).le, fun h =>
    (height_pos x).ne' (congrArg (fun p : ℂ × ℝ => p.2) h)⟩

theorem compactifiedQuadratic_interiorPoint (x : UpperHalfSpace) (v : ℂ × ℝ) :
    compactifiedQuadratic (interiorPoint x) v =
      boundaryFactor (interiorPoint x) ^ 2 * hyperbolicQuadratic x v := by
  change (‖v.1‖ ^ 2 + v.2 ^ 2) / radius (interiorPoint x) ^ 2 =
    ((coordinates x).2 / radius (interiorPoint x)) ^ 2 *
      ((‖v.1‖ ^ 2 + v.2 ^ 2) / (coordinates x).2 ^ 2)
  field_simp [(height_pos x).ne', (radius_pos (interiorPoint x)).ne']

theorem compactifiedQuadratic_boundary (x : CompactifiedCover) (hx : x.val.2 = 0) (v : ℂ) :
    compactifiedQuadratic x (v, 0) = ‖v‖ ^ 2 / ‖x.val.1‖ ^ 2 := by
  simp [compactifiedQuadratic, radius_sq, radiusSq, hx]

private def interiorCoverHomeomorph :
    UpperHalfSpace ≃ₜ {x : CompactifiedCover // 0 < x.val.2} where
  toFun x := ⟨interiorPoint x, height_pos x⟩
  invFun x := ⟨WithLp.toLp 2 x.val.val, x.property⟩
  left_inv x := Subtype.ext ((WithLp.equiv 2 (ℂ × ℝ)).symm_apply_apply x.val)
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := (continuous_coordinates.subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((WithLp.prod_continuous_toLp 2 ℂ ℝ).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

private theorem interiorPoint_isOpenEmbedding : IsOpenEmbedding interiorPoint := by
  have hopen : IsOpen {x : CompactifiedCover | 0 < x.val.2} :=
    isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)
  exact hopen.isOpenEmbedding_subtypeVal.comp interiorCoverHomeomorph.isOpenEmbedding

private theorem norm_scale_phase (a : ℝ) (ha : 0 ≤ a) (s : ℝ) (z : ℂ) :
    ‖(a : ℂ) * phase s * z‖ = a * ‖z‖ := by
  simp only [norm_mul, Complex.norm_of_nonneg ha, norm_phase, mul_one]

namespace Loxodromic

variable (g : Loxodromic)

private theorem radiusSq_tangentMap (n : ℤ) (p : ℂ × ℝ) :
    radiusSq (g.tangentMap n p) = (g.rho ^ n) ^ 2 * radiusSq p := by
  simp only [radiusSq, tangentMap_apply, multiplier,
    norm_scale_phase _ (zpow_pos g.rho_pos n).le]
  ring

/-- The literal loxodromic action on the compactified cover. -/
def compactAct (n : ℤ) (x : CompactifiedCover) : CompactifiedCover :=
  ⟨g.tangentMap n x.val,
    mul_nonneg (zpow_pos g.rho_pos n).le x.property.1, by
      intro h
      have hpos : 0 < radiusSq (g.tangentMap n x.val) := by
        rw [g.radiusSq_tangentMap]
        exact mul_pos (pow_pos (zpow_pos g.rho_pos n) 2) (radiusSq_pos x.property.2)
      simp [h, radiusSq] at hpos⟩

theorem compactAct_val (n : ℤ) (x : CompactifiedCover) :
    (g.compactAct n x).val = (g.multiplier n * x.val.1, g.rho ^ n * x.val.2) :=
  rfl

theorem compactAct_interiorPoint (n : ℤ) (x : UpperHalfSpace) :
    g.compactAct n (interiorPoint x) = interiorPoint (g.act n x) :=
  Subtype.ext rfl

theorem continuous_compactAct (n : ℤ) : Continuous (g.compactAct n) :=
  ((g.tangentMap n).continuous.comp continuous_subtype_val).subtype_mk _

@[instance_reducible]
def compactIntegerAction : AddAction ℤ CompactifiedCover where
  vadd := g.compactAct
  zero_vadd x := by
    change g.compactAct 0 x = x
    apply Subtype.ext
    simp [compactAct_val, multiplier, phase_zero]
  add_vadd m n x := by
    change g.compactAct (m + n) x = g.compactAct m (g.compactAct n x)
    apply Subtype.ext
    simp only [compactAct_val, g.multiplier_add, zpow_add₀ g.rho_pos.ne' m n, mul_assoc]

theorem radius_compactAct (n : ℤ) (x : CompactifiedCover) :
    radius (g.compactAct n x) = g.rho ^ n * radius x := by
  change Real.sqrt (radiusSq (g.tangentMap n x.val)) = g.rho ^ n * Real.sqrt (radiusSq x.val)
  rw [g.radiusSq_tangentMap, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (zpow_pos g.rho_pos n).le]

theorem boundaryFactor_compactAct (n : ℤ) (x : CompactifiedCover) :
    boundaryFactor (g.compactAct n x) = boundaryFactor x := by
  simp only [boundaryFactor, g.compactAct_val, g.radius_compactAct]
  exact mul_div_mul_left _ _ (zpow_pos g.rho_pos n).ne'

theorem compactifiedQuadratic_compactAct (n : ℤ) (x : CompactifiedCover) (v : ℂ × ℝ) :
    compactifiedQuadratic (g.compactAct n x) (g.tangentMap n v) = compactifiedQuadratic x v := by
  unfold compactifiedQuadratic
  rw [g.radiusSq_tangentMap, g.radius_compactAct, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 (zpow_pos g.rho_pos n).ne')]

/-- Logarithmic radius normalized so that one generator adds one. -/
def compactTime (x : CompactifiedCover) : ℝ := Real.log (radius x) / Real.log g.rho

private def radiusAt (t : ℝ) : ℝ := Real.exp (t * Real.log g.rho)

private theorem radiusAt_pos (t : ℝ) : 0 < g.radiusAt t := Real.exp_pos _

private theorem radiusAt_compactTime (x : CompactifiedCover) :
    g.radiusAt (g.compactTime x) = radius x := by
  rw [radiusAt, compactTime, div_mul_cancel₀ _ g.log_rho_ne_zero, Real.exp_log (radius_pos x)]

private theorem compactTime_compactAct (n : ℤ) (x : CompactifiedCover) :
    g.compactTime (g.compactAct n x) = g.compactTime x + (n : ℝ) := by
  unfold compactTime
  rw [g.radius_compactAct, Real.log_mul (zpow_pos g.rho_pos n).ne' (radius_pos x).ne',
    Real.log_zpow, add_div, mul_div_assoc, div_self g.log_rho_ne_zero, mul_one, add_comm]

private def diskCoordinate (x : CompactifiedCover) : ℂ :=
  phase (-g.theta * g.compactTime x) * x.val.1 / (radius x : ℂ)

private theorem norm_diskCoordinate (x : CompactifiedCover) :
    ‖g.diskCoordinate x‖ = ‖x.val.1‖ / radius x := by
  simp only [diskCoordinate, norm_div, norm_mul, norm_phase, one_mul,
    Complex.norm_of_nonneg (radius_pos x).le]

private def toPolar (x : CompactifiedCover) : ℝ × ClosedDisk :=
  (g.compactTime x, ⟨g.diskCoordinate x, mem_closedBall_zero_iff.mpr (by
    rw [g.norm_diskCoordinate x, div_le_iff₀ (radius_pos x), one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (radius_pos x).le).mp
    rw [radius_sq]
    exact le_add_of_nonneg_right (sq_nonneg _))⟩)

private theorem diskHeightSq_nonneg (u : ClosedDisk) : 0 ≤ 1 - ‖u.val‖ ^ 2 := by
  have hu := (sq_le_sq₀ (norm_nonneg u.val) zero_le_one).mpr
    (mem_closedBall_zero_iff.mp u.property)
  simpa only [sub_nonneg, one_pow] using hu

private def fromPolarPoint (p : ℝ × ClosedDisk) : ℂ × ℝ :=
  let R := g.radiusAt p.1
  ((R : ℂ) * phase (g.theta * p.1) * p.2.val, R * Real.sqrt (1 - ‖p.2.val‖ ^ 2))

private theorem radiusSq_fromPolarPoint (p : ℝ × ClosedDisk) :
    radiusSq (g.fromPolarPoint p) = g.radiusAt p.1 ^ 2 := by
  simp only [fromPolarPoint, radiusSq, norm_scale_phase _ (g.radiusAt_pos p.1).le,
    mul_pow, Real.sq_sqrt (diskHeightSq_nonneg p.2)]
  ring

private def fromPolar (p : ℝ × ClosedDisk) : CompactifiedCover :=
  ⟨g.fromPolarPoint p,
    mul_nonneg (g.radiusAt_pos p.1).le (Real.sqrt_nonneg _), by
      intro h
      have hsq := g.radiusSq_fromPolarPoint p
      rw [h] at hsq
      have hne : g.radiusAt p.1 ^ 2 ≠ 0 := (pow_pos (g.radiusAt_pos p.1) 2).ne'
      exact hne (by simpa [radiusSq] using hsq.symm)⟩

private theorem radius_fromPolar (p : ℝ × ClosedDisk) :
    radius (g.fromPolar p) = g.radiusAt p.1 := by
  change Real.sqrt (radiusSq (g.fromPolarPoint p)) = _
  rw [g.radiusSq_fromPolarPoint, Real.sqrt_sq (g.radiusAt_pos p.1).le]

private theorem compactTime_fromPolar (p : ℝ × ClosedDisk) :
    g.compactTime (g.fromPolar p) = p.1 := by
  rw [compactTime, g.radius_fromPolar, radiusAt, Real.log_exp,
    mul_div_cancel_right₀ _ g.log_rho_ne_zero]

private theorem fromPolar_toPolar (x : CompactifiedCover) :
    g.fromPolar (g.toPolar x) = x := by
  apply Subtype.ext
  change ((g.radiusAt (g.compactTime x) : ℂ) * phase (g.theta * g.compactTime x) *
      g.diskCoordinate x, g.radiusAt (g.compactTime x) *
        Real.sqrt (1 - ‖g.diskCoordinate x‖ ^ 2)) = x.val
  rw [g.radiusAt_compactTime]
  refine Prod.ext ?_ ?_
  · have hR : (radius x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radius_pos x).ne'
    have hp : phase (g.theta * g.compactTime x) * phase (-g.theta * g.compactTime x) = 1 := by
      rw [neg_mul, mul_comm, phase_neg_mul]
    calc
      _ = (phase (g.theta * g.compactTime x) * phase (-g.theta * g.compactTime x)) *
          ((radius x : ℂ) * x.val.1 / (radius x : ℂ)) := by unfold diskCoordinate; ring
      _ = _ := by rw [hp, one_mul, mul_div_cancel_left₀ _ hR]
  · apply (sq_eq_sq₀ (mul_nonneg (radius_pos x).le (Real.sqrt_nonneg _)) x.property.1).mp
    have hs := Real.sq_sqrt (diskHeightSq_nonneg (g.toPolar x).2)
    change Real.sqrt (1 - ‖g.diskCoordinate x‖ ^ 2) ^ 2 =
      1 - ‖g.diskCoordinate x‖ ^ 2 at hs
    rw [mul_pow, hs, g.norm_diskCoordinate, div_pow, mul_sub, mul_one, ← mul_div_assoc,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 (radius_pos x).ne'), radius_sq, radiusSq]
    ring

private theorem toPolar_fromPolar (p : ℝ × ClosedDisk) :
    g.toPolar (g.fromPolar p) = p := by
  refine Prod.ext (g.compactTime_fromPolar p) (Subtype.ext ?_)
  change phase (-g.theta * g.compactTime (g.fromPolar p)) *
      ((g.radiusAt p.1 : ℂ) * phase (g.theta * p.1) * p.2.val) /
      (radius (g.fromPolar p) : ℂ) = p.2.val
  rw [g.compactTime_fromPolar, g.radius_fromPolar]
  have hR : (g.radiusAt p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (g.radiusAt_pos p.1).ne'
  have hp : phase (-g.theta * p.1) * phase (g.theta * p.1) = 1 := by
    rw [neg_mul, phase_neg_mul]
  calc
    _ = (g.radiusAt p.1 : ℂ) * ((phase (-g.theta * p.1) * phase (g.theta * p.1)) *
        p.2.val) / (g.radiusAt p.1 : ℂ) := by ring
    _ = _ := by rw [hp, one_mul, mul_div_cancel_left₀ _ hR]

/-- The explicit compactified cover coordinates `(t, u)`. -/
def compactCoverHomeomorph : CompactifiedCover ≃ₜ ℝ × ClosedDisk where
  toFun := g.toPolar
  invFun := g.fromPolar
  left_inv := g.fromPolar_toPolar
  right_inv := g.toPolar_fromPolar
  continuous_toFun := by
    have hlog : Continuous (fun x => Real.log (radius x)) :=
      continuous_iff_continuousAt.2 fun x =>
        (Real.continuousAt_log (radius_pos x).ne').comp continuous_radius.continuousAt
    have ht : Continuous g.compactTime := hlog.div_const _
    have hu : Continuous g.diskCoordinate :=
      ((continuous_phase.comp (continuous_const.mul ht)).mul
        (continuous_fst.comp continuous_subtype_val)).div
        (Complex.continuous_ofReal.comp continuous_radius)
        (fun x => Complex.ofReal_ne_zero.mpr (radius_pos x).ne')
    exact ht.prodMk (hu.subtype_mk _)
  continuous_invFun := by
    have hR : Continuous (fun p : ℝ × ClosedDisk => g.radiusAt p.1) :=
      Real.continuous_exp.comp (continuous_fst.mul continuous_const)
    have hu : Continuous (fun p : ℝ × ClosedDisk => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hz : Continuous (fun p : ℝ × ClosedDisk =>
        (g.radiusAt p.1 : ℂ) * phase (g.theta * p.1) * p.2.val) :=
      ((Complex.continuous_ofReal.comp hR).mul
        (continuous_phase.comp (continuous_const.mul continuous_fst))).mul hu
    exact (hz.prodMk (hR.mul ((continuous_const.sub (hu.norm.pow 2)).sqrt))).subtype_mk _

theorem compactCoverHomeomorph_apply (x : CompactifiedCover) :
    (g.compactCoverHomeomorph x).1 = Real.log (radius x) / Real.log g.rho ∧
    (g.compactCoverHomeomorph x).2.val =
      phase (-g.theta * g.compactTime x) * x.val.1 / (radius x : ℂ) :=
  ⟨rfl, rfl⟩

theorem compactCoverHomeomorph_symm_val (p : ℝ × ClosedDisk) :
    (g.compactCoverHomeomorph.symm p).val =
      let R := Real.exp (p.1 * Real.log g.rho)
      ((R : ℂ) * phase (g.theta * p.1) * p.2.val, R * Real.sqrt (1 - ‖p.2.val‖ ^ 2)) :=
  rfl

/-- The same generator acts by integer translation of `t` and fixes `u`. -/
theorem compactCoverHomeomorph_act (n : ℤ) (x : CompactifiedCover) :
    g.compactCoverHomeomorph (g.compactAct n x) =
      ((g.compactCoverHomeomorph x).1 + (n : ℝ), (g.compactCoverHomeomorph x).2) := by
  refine Prod.ext (g.compactTime_compactAct n x) (Subtype.ext ?_)
  change g.diskCoordinate (g.compactAct n x) = g.diskCoordinate x
  have hp : phase (-g.theta * (g.compactTime x + (n : ℝ))) * phase ((n : ℝ) * g.theta) =
      phase (-g.theta * g.compactTime x) := by
    rw [← phase_add]
    congr 1
    ring
  have hR : ((g.rho ^ n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zpow_pos g.rho_pos n).ne'
  simp only [diskCoordinate, g.compactTime_compactAct, g.compactAct_val,
    g.radius_compactAct, multiplier, Complex.ofReal_mul]
  calc
    _ = ((g.rho ^ n : ℝ) : ℂ) *
        ((phase (-g.theta * (g.compactTime x + (n : ℝ))) * phase ((n : ℝ) * g.theta)) *
          x.val.1) / (((g.rho ^ n : ℝ) : ℂ) * (radius x : ℂ)) := by ring
    _ = _ := by rw [hp, mul_div_mul_left _ _ hR]

theorem height_eq_zero_iff (x : CompactifiedCover) :
    x.val.2 = 0 ↔ ‖(g.compactCoverHomeomorph x).2.val‖ = 1 := by
  change x.val.2 = 0 ↔ ‖g.diskCoordinate x‖ = 1
  rw [g.norm_diskCoordinate, div_eq_iff (radius_pos x).ne', one_mul,
    ← sq_eq_sq₀ (norm_nonneg _) (radius_pos x).le, radius_sq, radiusSq]
  constructor
  · intro hx
    simp [hx]
  · intro h
    apply (sq_eq_sq₀ x.property.1 (show 0 ≤ (0 : ℝ) from le_rfl)).mp
    nlinarith

def compactOrbitSetoid : Setoid CompactifiedCover :=
  letI := g.compactIntegerAction
  AddAction.orbitRel ℤ CompactifiedCover

theorem compactOrbitSetoid_iff (x y : CompactifiedCover) :
    g.compactOrbitSetoid x y ↔ ∃ n : ℤ, g.compactAct n y = x :=
  Iff.rfl

/-- The orbit space with the quotient topology of the compactified cover. -/
abbrev CompactifiedQuotient := Quotient g.compactOrbitSetoid

private def diskCircleProjection : ClosedDisk × ℝ → ClosedDisk × AddCircle (1 : ℝ) :=
  Prod.map id ((↑) : ℝ → AddCircle (1 : ℝ))

def compactOrbitCoordinates (x : CompactifiedCover) : ClosedDisk × AddCircle (1 : ℝ) :=
  diskCircleProjection ((Homeomorph.prodComm ℝ ClosedDisk) (g.compactCoverHomeomorph x))

theorem compactOrbitCoordinates_fiber_iff (x y : CompactifiedCover) :
    g.compactOrbitCoordinates x = g.compactOrbitCoordinates y ↔
      ∃ n : ℤ, g.compactAct n y = x := by
  constructor
  · intro h
    have hu : (g.compactCoverHomeomorph x).2 = (g.compactCoverHomeomorph y).2 :=
      congrArg Prod.fst h
    have ht : ((g.compactCoverHomeomorph x).1 : AddCircle (1 : ℝ)) =
        ((g.compactCoverHomeomorph y).1 : AddCircle (1 : ℝ)) := congrArg Prod.snd h
    obtain ⟨n, hn⟩ := (circle_eq_iff _ _).mp ht
    refine ⟨n, g.compactCoverHomeomorph.injective ?_⟩
    rw [g.compactCoverHomeomorph_act]
    exact Prod.ext hn.symm hu.symm
  · rintro ⟨n, rfl⟩
    unfold compactOrbitCoordinates
    rw [g.compactCoverHomeomorph_act]
    exact Prod.ext rfl ((circle_eq_iff _ _).mpr ⟨n, rfl⟩)

private theorem compactOrbitCoordinates_isOpenQuotientMap :
    IsOpenQuotientMap g.compactOrbitCoordinates := by
  have hcircle : IsOpenQuotientMap diskCircleProjection :=
    IsOpenQuotientMap.id.prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
  exact hcircle.comp
    (g.compactCoverHomeomorph.trans (Homeomorph.prodComm ℝ ClosedDisk)).isOpenQuotientMap

private def compactQuotientCoordinates : g.CompactifiedQuotient → ClosedDisk × AddCircle (1 : ℝ) :=
  Quotient.lift g.compactOrbitCoordinates fun x y h =>
    (g.compactOrbitCoordinates_fiber_iff x y).2 ((g.compactOrbitSetoid_iff x y).1 h)

/-- The compactified cyclic quotient is a closed disk times a circle. -/
def solidTorusHomeomorph : g.CompactifiedQuotient ≃ₜ ClosedDisk × AddCircle (1 : ℝ) := by
  let q := Quotient.mk g.compactOrbitSetoid
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  have hcoords := g.compactOrbitCoordinates_isOpenQuotientMap
  have hcomp : g.compactQuotientCoordinates ∘ q = g.compactOrbitCoordinates := rfl
  have hcont : Continuous g.compactQuotientCoordinates :=
    hq.continuous_iff.mpr (by rw [hcomp]; exact hcoords.continuous)
  have hopen : IsOpenMap g.compactQuotientCoordinates :=
    IsOpenMap.of_comp hq.continuous hq.surjective (by rw [hcomp]; exact hcoords.isOpenMap)
  have hinj : Injective g.compactQuotientCoordinates := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y hxy
    exact Quotient.sound
      ((g.compactOrbitSetoid_iff x y).2 ((g.compactOrbitCoordinates_fiber_iff x y).1 hxy))
  have hsurj : Surjective g.compactQuotientCoordinates := by
    intro p
    obtain ⟨x, hx⟩ := hcoords.surjective p
    exact ⟨q x, hx⟩
  exact (Equiv.ofBijective g.compactQuotientCoordinates ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    hcont hopen

theorem solidTorusHomeomorph_mk (x : CompactifiedCover) :
    g.solidTorusHomeomorph (Quotient.mk g.compactOrbitSetoid x) =
      ((g.compactCoverHomeomorph x).2, ((g.compactCoverHomeomorph x).1 : AddCircle (1 : ℝ))) :=
  rfl

theorem compactifiedQuotient_isCompact : CompactSpace g.CompactifiedQuotient := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let : CompactSpace ClosedDisk :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  exact g.solidTorusHomeomorph.symm.compactSpace

theorem compactQuotientProjection_isOpenQuotientMap :
    IsOpenQuotientMap (Quotient.mk g.compactOrbitSetoid) := by
  have hcomp : (g.solidTorusHomeomorph.symm : ClosedDisk × AddCircle (1 : ℝ) →
        g.CompactifiedQuotient) ∘ g.compactOrbitCoordinates =
      (Quotient.mk g.compactOrbitSetoid) := by
    funext x
    exact g.solidTorusHomeomorph.symm_apply_apply (Quotient.mk g.compactOrbitSetoid x)
  rw [← hcomp]
  exact g.solidTorusHomeomorph.symm.isOpenQuotientMap.comp
    g.compactOrbitCoordinates_isOpenQuotientMap

private theorem compactAct_height_eq_zero (n : ℤ) (x : CompactifiedCover) :
    (g.compactAct n x).val.2 = 0 ↔ x.val.2 = 0 := by
  rw [g.compactAct_val, mul_eq_zero]
  simp only [(zpow_pos g.rho_pos n).ne', false_or]

/-- The added boundary consists of the orbits at height zero. -/
def IsBoundary : g.CompactifiedQuotient → Prop :=
  Quotient.lift (fun x : CompactifiedCover => x.val.2 = 0) fun x y h => by
    obtain ⟨n, hn⟩ := (g.compactOrbitSetoid_iff x y).1 h
    rw [← hn]
    exact propext (g.compactAct_height_eq_zero n y)

abbrev Boundary := {q : g.CompactifiedQuotient // g.IsBoundary q}

theorem isBoundary_mk (x : CompactifiedCover) :
    g.IsBoundary (Quotient.mk g.compactOrbitSetoid x) ↔ x.val.2 = 0 :=
  Iff.rfl

theorem isBoundary_iff (q : g.CompactifiedQuotient) :
    g.IsBoundary q ↔ ‖(g.solidTorusHomeomorph q).1.val‖ = 1 := by
  refine Quotient.inductionOn q fun x => ?_
  rw [g.solidTorusHomeomorph_mk]
  exact g.height_eq_zero_iff x

private def diskOfCircle (u : Circle) : ClosedDisk :=
  ⟨(u : ℂ), mem_closedBall_zero_iff.mpr (Circle.norm_coe u).le⟩

private def unitEdgeHomeomorph :
    {p : ClosedDisk × AddCircle (1 : ℝ) // ‖p.1.val‖ = 1} ≃ₜ Circle × AddCircle (1 : ℝ) where
  toFun p := (⟨p.val.1.val, mem_sphere_zero_iff_norm.mpr p.property⟩, p.val.2)
  invFun p := ⟨(diskOfCircle p.1, p.2), Circle.norm_coe p.1⟩
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext rfl) rfl)
  right_inv _ := Prod.ext (Circle.ext rfl) rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
      continuous_snd).subtype_mk _

/-- The restriction of the solid-torus coordinates to the literal height-zero orbits. -/
def boundaryCircleHomeomorph : g.Boundary ≃ₜ Circle × AddCircle (1 : ℝ) :=
  (g.solidTorusHomeomorph.subtype g.isBoundary_iff).trans unitEdgeHomeomorph

def boundaryTorusHomeomorph : g.Boundary ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ) :=
  g.boundaryCircleHomeomorph.trans
    ((AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.prodCongr (Homeomorph.refl _))

theorem boundaryCircleHomeomorph_coordinates (q : g.Boundary) :
    (g.boundaryCircleHomeomorph q).1.val = (g.solidTorusHomeomorph q.val).1.val ∧
      (g.boundaryCircleHomeomorph q).2 = (g.solidTorusHomeomorph q.val).2 :=
  ⟨rfl, rfl⟩

/-- The original quotient maps into this compactification by including positive heights. -/
def interiorQuotientInclusion : g.OrbitQuotient → g.CompactifiedQuotient :=
  Quotient.lift (fun x => Quotient.mk g.compactOrbitSetoid (interiorPoint x)) fun x y h => by
    obtain ⟨n, hn⟩ := (g.orbitSetoid_iff x y).1 h
    apply Quotient.sound
    exact (g.compactOrbitSetoid_iff _ _).2 ⟨n, by rw [g.compactAct_interiorPoint, hn]⟩

theorem interiorQuotientInclusion_isOpenEmbedding : IsOpenEmbedding g.interiorQuotientInclusion := by
  let q := Quotient.mk g.orbitSetoid
  have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
  have hp := g.compactQuotientProjection_isOpenQuotientMap
  have hcont : Continuous (g.interiorQuotientInclusion ∘ q) :=
    hp.continuous.comp interiorPoint_isOpenEmbedding.continuous
  have hopen : IsOpenMap (g.interiorQuotientInclusion ∘ q) :=
    hp.isOpenMap.comp interiorPoint_isOpenEmbedding.isOpenMap
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (hq.continuous_iff.2 hcont) ?_
    (IsOpenMap.of_comp hq.continuous hq.surjective hopen)
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y hxy
  have hrel : g.compactOrbitSetoid (interiorPoint x) (interiorPoint y) := Quotient.exact hxy
  obtain ⟨n, hn⟩ := (g.compactOrbitSetoid_iff _ _).1 hrel
  rw [g.compactAct_interiorPoint] at hn
  exact Quotient.sound
    ((g.orbitSetoid_iff _ _).2 ⟨n, interiorPoint_isOpenEmbedding.injective hn⟩)

theorem mem_range_interiorQuotientInclusion_iff (q : g.CompactifiedQuotient) :
    q ∈ Set.range g.interiorQuotientInclusion ↔ ¬ g.IsBoundary q := by
  constructor
  · rintro ⟨a, rfl⟩
    refine Quotient.inductionOn a fun x => ?_
    exact (height_pos x).ne'
  · refine Quotient.inductionOn q fun x => ?_
    intro hx
    have hne : x.val.2 ≠ 0 := fun he => hx ((g.isBoundary_mk x).2 he)
    let y : UpperHalfSpace := ⟨WithLp.toLp 2 x.val, lt_of_le_of_ne x.property.1 hne.symm⟩
    exact ⟨Quotient.mk g.orbitSetoid y, congrArg (Quotient.mk g.compactOrbitSetoid)
      (Subtype.ext rfl : interiorPoint y = x)⟩

theorem interiorQuotientInclusion_dense : DenseRange g.interiorQuotientInclusion := by
  have hdisk : Dense {u : ClosedDisk | ‖u.val‖ < 1} := by
    apply Subtype.dense_iff.mpr
    have himage : Subtype.val '' {u : ClosedDisk | ‖u.val‖ < 1} = Metric.ball (0 : ℂ) 1 := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact mem_ball_zero_iff.mpr hu
      · intro hz
        have hnorm := mem_ball_zero_iff.mp hz
        exact ⟨⟨z, mem_closedBall_zero_iff.mpr hnorm.le⟩, hnorm, rfl⟩
    rw [himage, closure_ball (0 : ℂ) one_ne_zero]
  have hprod : Dense
      ({u : ClosedDisk | ‖u.val‖ < 1} ×ˢ (Set.univ : Set (AddCircle (1 : ℝ)))) :=
    hdisk.prod dense_univ
  have hpre : Set.range g.interiorQuotientInclusion =
      g.solidTorusHomeomorph ⁻¹'
        ({u : ClosedDisk | ‖u.val‖ < 1} ×ˢ (Set.univ : Set (AddCircle (1 : ℝ)))) := by
    ext q
    rw [g.mem_range_interiorQuotientInclusion_iff, g.isBoundary_iff]
    change (¬ ‖(g.solidTorusHomeomorph q).1.val‖ = 1) ↔
      (‖(g.solidTorusHomeomorph q).1.val‖ < 1 ∧ True)
    rw [and_true]
    exact ⟨fun h => lt_of_le_of_ne
      (mem_closedBall_zero_iff.mp (g.solidTorusHomeomorph q).1.property) h, ne_of_lt⟩
  change Dense (Set.range g.interiorQuotientInclusion)
  rw [hpre]
  exact hprod.preimage g.solidTorusHomeomorph.isOpenMap

theorem boundary_eq_frontier_interior :
    {q : g.CompactifiedQuotient | g.IsBoundary q} =
      frontier (Set.range g.interiorQuotientInclusion) := by
  rw [frontier, g.interiorQuotientInclusion_dense.closure_range,
    g.interiorQuotientInclusion_isOpenEmbedding.isOpen_range.interior_eq]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, true_and,
    g.mem_range_interiorQuotientInclusion_iff, not_not]

/-- Filling the boundary circle at fixed longitudinal coordinate by the corresponding disk. -/
def meridianDisk (t : ℝ) (u : ClosedDisk) : g.CompactifiedQuotient :=
  Quotient.mk g.compactOrbitSetoid (g.compactCoverHomeomorph.symm (t, u))

theorem continuous_meridianDisk (t : ℝ) : Continuous (g.meridianDisk t) :=
  g.compactQuotientProjection_isOpenQuotientMap.continuous.comp
    (g.compactCoverHomeomorph.symm.continuous.comp (continuous_const.prodMk continuous_id))

theorem solidTorusHomeomorph_meridianDisk (t : ℝ) (u : ClosedDisk) :
    g.solidTorusHomeomorph (g.meridianDisk t u) = (u, (t : AddCircle (1 : ℝ))) := by
  rw [meridianDisk, g.solidTorusHomeomorph_mk, g.compactCoverHomeomorph.apply_symm_apply]

theorem meridianDisk_injective (t : ℝ) : Injective (g.meridianDisk t) := by
  intro u v h
  have h' := congrArg (fun q => (g.solidTorusHomeomorph q).1) h
  simpa only [g.solidTorusHomeomorph_meridianDisk] using h'

theorem meridianDisk_boundary_iff (t : ℝ) (u : ClosedDisk) :
    g.IsBoundary (g.meridianDisk t u) ↔ ‖u.val‖ = 1 := by
  rw [g.isBoundary_iff, g.solidTorusHomeomorph_meridianDisk]

def meridianCircle (t : ℝ) (u : Circle) : g.Boundary :=
  ⟨g.meridianDisk t (diskOfCircle u), (g.meridianDisk_boundary_iff t _).2 (Circle.norm_coe u)⟩

theorem boundaryCircleHomeomorph_meridianCircle (t : ℝ) (u : Circle) :
    g.boundaryCircleHomeomorph (g.meridianCircle t u) = (u, (t : AddCircle (1 : ℝ))) := by
  obtain ⟨hu, ht⟩ := g.boundaryCircleHomeomorph_coordinates (g.meridianCircle t u)
  change _ = (g.solidTorusHomeomorph (g.meridianDisk t (diskOfCircle u))).1.val at hu
  change _ = (g.solidTorusHomeomorph (g.meridianDisk t (diskOfCircle u))).2 at ht
  rw [g.solidTorusHomeomorph_meridianDisk] at hu ht
  exact Prod.ext (Circle.ext hu) ht

private def expBoundaryPoint (z : ℂ) : CompactifiedCover :=
  ⟨(Function.Periodic.qParam 1 z, 0), le_rfl, fun h =>
    Function.Periodic.qParam_ne_zero (h := 1) z (congrArg (fun p : ℂ × ℝ => p.1) h)⟩

/-- The literal boundary lift sends `z` to the orbit of `(exp (2πiz), 0)`. -/
def boundaryLift (z : ℂ) : g.Boundary :=
  ⟨Quotient.mk g.compactOrbitSetoid (expBoundaryPoint z), (g.isBoundary_mk _).2 rfl⟩

theorem continuous_boundaryLift : Continuous g.boundaryLift := by
  have hx : Continuous expBoundaryPoint :=
    ((Function.Periodic.continuous_qParam (h := 1)).prodMk continuous_const).subtype_mk _
  exact (g.compactQuotientProjection_isOpenQuotientMap.continuous.comp hx).subtype_mk _

theorem surjective_boundaryLift : Surjective g.boundaryLift := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.exists_rep q.val
  have hp : g.IsBoundary (Quotient.mk g.compactOrbitSetoid x) := by
    rw [hx]
    exact q.property
  have hr : x.val.2 = 0 := (g.isBoundary_mk x).mp hp
  have hz : x.val.1 ≠ 0 := fun he => x.property.2 (Prod.ext he hr)
  refine ⟨Function.Periodic.invQParam 1 x.val.1, Subtype.ext ?_⟩
  change Quotient.mk g.compactOrbitSetoid
    (expBoundaryPoint (Function.Periodic.invQParam 1 x.val.1)) = q.val
  refine (congrArg (Quotient.mk g.compactOrbitSetoid)
    (Subtype.ext (Prod.ext ?_ hr.symm))).trans hx
  exact Function.Periodic.qParam_right_inv one_ne_zero hz

private theorem qParam_one_eq_exp (z : ℂ) :
    Function.Periodic.qParam 1 z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) := by
  simp [Function.Periodic.qParam]

private theorem ofTau_compactAct_expBoundaryPoint (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ) (z : ℂ) :
    (ofTau τ hτ).compactAct n (expBoundaryPoint z) = expBoundaryPoint (z + (n : ℂ) * τ) := by
  apply Subtype.ext
  rw [compactAct_val]
  refine Prod.ext ?_ (mul_zero _)
  change (ofTau τ hτ).multiplier n * Function.Periodic.qParam 1 z =
    Function.Periodic.qParam 1 (z + (n : ℂ) * τ)
  rw [ofTau_multiplier, qParam_one_eq_exp, qParam_one_eq_exp, ← Complex.exp_int_mul,
    ← Complex.exp_add]
  congr 1
  ring

/-- The boundary seen in the complex lift has precisely the lattice periods `1` and `τ`. -/
theorem boundaryLift_eq_iff (τ : ℂ) (hτ : 0 < τ.im) (z w : ℂ) :
    (ofTau τ hτ).boundaryLift z = (ofTau τ hτ).boundaryLift w ↔
      ∃ m n : ℤ, z - w = (m : ℂ) + (n : ℂ) * τ := by
  have horbit :
      (ofTau τ hτ).boundaryLift z = (ofTau τ hτ).boundaryLift w ↔
        ∃ n : ℤ, expBoundaryPoint (w + (n : ℂ) * τ) = expBoundaryPoint z := by
    constructor
    · intro h
      have hrel : (ofTau τ hτ).compactOrbitSetoid (expBoundaryPoint z) (expBoundaryPoint w) :=
        Quotient.exact (congrArg Subtype.val h)
      obtain ⟨n, hn⟩ := ((ofTau τ hτ).compactOrbitSetoid_iff _ _).mp hrel
      exact ⟨n, (ofTau_compactAct_expBoundaryPoint τ hτ n w).symm.trans hn⟩
    · rintro ⟨n, hn⟩
      apply Subtype.ext
      apply Quotient.sound
      exact ((ofTau τ hτ).compactOrbitSetoid_iff _ _).mpr
        ⟨n, (ofTau_compactAct_expBoundaryPoint τ hτ n w).trans hn⟩
  rw [horbit]
  constructor
  · rintro ⟨n, hn⟩
    have he : Function.Periodic.qParam 1 z = Function.Periodic.qParam 1 (w + (n : ℂ) * τ) :=
      congrArg (fun p : CompactifiedCover => p.val.1) hn.symm
    rw [qParam_one_eq_exp, qParam_one_eq_exp] at he
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    have hscaled : (2 * (Real.pi : ℂ) * Complex.I) * z =
        (2 * (Real.pi : ℂ) * Complex.I) * (w + (m : ℂ) + (n : ℂ) * τ) := by
      rw [hm]
      ring
    have hz := mul_left_cancel₀ Complex.two_pi_I_ne_zero hscaled
    exact ⟨m, n, by rw [hz]; ring⟩
  · rintro ⟨m, n, h⟩
    have hz : z = w + (m : ℂ) + (n : ℂ) * τ := by
      calc
        z = w + (z - w) := by ring
        _ = _ := by rw [h]; ring
    refine ⟨n, Subtype.ext (Prod.ext ?_ rfl)⟩
    change Function.Periodic.qParam 1 (w + (n : ℂ) * τ) = Function.Periodic.qParam 1 z
    rw [qParam_one_eq_exp, qParam_one_eq_exp]
    symm
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨m, by rw [hz]; ring⟩

end Loxodromic

end D5.S3.Geometry.AdS3LoxodromicQuotient
