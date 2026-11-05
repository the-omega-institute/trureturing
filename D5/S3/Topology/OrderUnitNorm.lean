/- GID: D5/S3/Topology/OrderUnitNorm
   generality: G
   mirror-B: D5/B/S3/Topology/OrderUnitNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Gauge]
   utility: none
   digest: Closed salient cones with interior units yield exact order norms and operator bounds. -/

module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Geometry.Convex.Cone.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

/-! The order norm is constructed from the specified cone and unit. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Pointwise Topology

namespace D5.S3.Topology.OrderUnitNorm

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original geometric cone and its specified interior order unit. -/
structure Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  cone : ConvexCone ℝ E
  unit : E
  zero_mem : (0 : E) ∈ cone
  closed : IsClosed (cone : Set E)
  salient : cone.Salient
  interior_unit : unit ∈ interior (cone : Set E)

namespace Data

variable (A : Data E)

/-- The symmetric interval defined by the original cone and unit. -/
def interval : Set E := {v | A.unit - v ∈ A.cone ∧ A.unit + v ∈ A.cone}

/-- Nonnegative radii, including the attained radius zero when the vector vanishes. -/
def radii (v : E) : Set ℝ :=
  {r | 0 ≤ r ∧ r • A.unit - v ∈ A.cone ∧ r • A.unit + v ∈ A.cone}

/-- The literal nonnegative-radius infimum of the order-unit norm. -/
def orderNorm (v : E) : ℝ := sInf (A.radii v)

private lemma unit_mem : A.unit ∈ A.cone := interior_subset A.interior_unit

private lemma interval_convex : Convex ℝ A.interval := by
  intro x hx y hy a b ha hb hab
  constructor
  · have he : A.unit - (a • x + b • y) =
        a • (A.unit - x) + b • (A.unit - y) := by
      match_scalars <;> linarith
    rw [he]
    exact A.cone.convex hx.1 hy.1 ha hb hab
  · have he : A.unit + (a • x + b • y) =
        a • (A.unit + x) + b • (A.unit + y) := by
      match_scalars <;> linarith
    rw [he]
    exact A.cone.convex hx.2 hy.2 ha hb hab

private lemma interval_balanced : Balanced ℝ A.interval := by
  apply (balanced_iff_neg_mem A.interval_convex).2
  intro x hx
  simpa [interval, sub_eq_add_neg] using And.intro hx.2 hx.1

private lemma interval_nhds : A.interval ∈ 𝓝 (0 : E) := by
  have hu := mem_interior_iff_mem_nhds.mp A.interior_unit
  have hm : Tendsto (fun v : E => A.unit - v) (𝓝 0) (𝓝 A.unit) := by
    have h : Continuous (fun v : E => A.unit - v) := by fun_prop
    simpa only [sub_zero] using h.tendsto (0 : E)
  have hp : Tendsto (fun v : E => A.unit + v) (𝓝 0) (𝓝 A.unit) := by
    have h : Continuous (fun v : E => A.unit + v) := by fun_prop
    simpa only [add_zero] using h.tendsto (0 : E)
  exact inter_mem (hm hu) (hp hu)

private lemma interval_absorbent : Absorbent ℝ A.interval :=
  absorbent_nhds_zero A.interval_nhds

private lemma smul_interval_iff {r : ℝ} (hr : 0 < r) (v : E) :
    v ∈ r • A.interval ↔ r • A.unit - v ∈ A.cone ∧ r • A.unit + v ∈ A.cone := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    constructor
    · simpa [smul_sub] using A.cone.smul_mem hr hw.1
    · simpa [smul_add] using A.cone.smul_mem hr hw.2
  · intro hv
    refine ⟨r⁻¹ • v, ?_, smul_inv_smul₀ hr.ne' v⟩
    constructor
    · simpa [smul_sub, smul_smul, hr.ne'] using A.cone.smul_mem (inv_pos.mpr hr) hv.1
    · simpa [smul_add, smul_smul, hr.ne'] using A.cone.smul_mem (inv_pos.mpr hr) hv.2

private lemma radii_nonempty (v : E) : (A.radii v).Nonempty := by
  obtain ⟨r, hr, hv⟩ := A.interval_absorbent.gauge_set_nonempty (x := v)
  exact ⟨r, hr.le, (A.smul_interval_iff hr v).mp hv⟩

private lemma radii_bdd (v : E) : BddBelow (A.radii v) :=
  ⟨0, fun _ hr => hr.1⟩

private lemma radii_closed (v : E) : IsClosed (A.radii v) := by
  exact isClosed_Ici.inter
    ((A.closed.preimage ((continuous_id.smul continuous_const).sub continuous_const)).inter
      (A.closed.preimage ((continuous_id.smul continuous_const).add continuous_const)))

private lemma norm_attained (v : E) : A.orderNorm v ∈ A.radii v :=
  (A.radii_closed v).csInf_mem (A.radii_nonempty v) (A.radii_bdd v)

private lemma norm_nonneg (v : E) : 0 ≤ A.orderNorm v := (A.norm_attained v).1

private lemma cone_smul_nonneg {r : ℝ} (hr : 0 ≤ r) {v : E} (hv : v ∈ A.cone) :
    r • v ∈ A.cone := by
  obtain rfl | hr := hr.eq_or_lt
  · simpa using A.zero_mem
  · exact A.cone.smul_mem hr hv

private lemma radii_upward {v : E} {r s : ℝ} (hr : r ∈ A.radii v) (hrs : r ≤ s) :
    s ∈ A.radii v := by
  have hd := A.cone_smul_nonneg (sub_nonneg.mpr hrs) A.unit_mem
  refine ⟨hr.1.trans hrs, ?_, ?_⟩
  · have he : s • A.unit - v = (r • A.unit - v) + (s-r) • A.unit := by module
    rw [he]
    exact A.cone.add_mem hr.2.1 hd
  · have he : s • A.unit + v = (r • A.unit + v) + (s-r) • A.unit := by module
    rw [he]
    exact A.cone.add_mem hr.2.2 hd

private lemma norm_le_iff (v : E) (r : ℝ) :
    A.orderNorm v ≤ r ↔ r ∈ A.radii v := by
  constructor
  · exact A.radii_upward (A.norm_attained v)
  · exact csInf_le (A.radii_bdd v)

private lemma norm_eq_gauge (v : E) : A.orderNorm v = gauge A.interval v := by
  apply le_antisymm
  · unfold gauge
    apply le_csInf (A.interval_absorbent.gauge_set_nonempty (x := v))
    intro r hr
    exact (A.norm_le_iff v r).mpr ⟨hr.1.le, (A.smul_interval_iff hr.1 v).mp hr.2⟩
  · apply le_of_forall_pos_lt_add
    intro ε hε
    have hr : 0 < A.orderNorm v + ε / 2 := by linarith [A.norm_nonneg v]
    have hv := (A.norm_le_iff v (A.orderNorm v + ε / 2)).mp (by linarith)
    exact (gauge_le_of_mem hr.le ((A.smul_interval_iff hr v).mpr hv.2)).trans_lt
      (by linarith)

private lemma norm_zero_iff (v : E) : A.orderNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hv := A.norm_attained v
    change 0 ≤ A.orderNorm v ∧
      A.orderNorm v • A.unit - v ∈ A.cone ∧
      A.orderNorm v • A.unit + v ∈ A.cone at hv
    rw [h] at hv
    simp only [zero_smul, zero_sub, zero_add] at hv
    by_contra hn
    exact A.salient v hv.2.2 hn hv.2.1
  · rintro rfl
    rw [A.norm_eq_gauge]
    exact gauge_zero

private def seminorm : Seminorm ℝ E :=
  gaugeSeminorm A.interval_balanced A.interval_convex A.interval_absorbent

private lemma seminorm_eq (v : E) : A.seminorm v = A.orderNorm v :=
  (A.norm_eq_gauge v).symm

/-- A copy of the original vector space carrying its proved order-unit norm. -/
def Space (_A : Data E) := E

instance : AddCommGroup A.Space := inferInstanceAs (AddCommGroup E)
instance : Module ℝ A.Space := inferInstanceAs (Module ℝ E)
instance : Norm A.Space := ⟨fun v => A.orderNorm v⟩

theorem norm_core : NormedSpace.Core ℝ A.Space where
  norm_nonneg := A.norm_nonneg
  norm_smul r v := by
    change A.orderNorm (r • v) = ‖r‖ * A.orderNorm v
    rw [← A.seminorm_eq (r • (v : E)), ← A.seminorm_eq (v : E)]
    exact map_smul_eq_mul A.seminorm r (v : E)
  norm_triangle v w := by
    change A.orderNorm (v + w) ≤ A.orderNorm v + A.orderNorm w
    rw [← A.seminorm_eq ((v : E) + (w : E)),
      ← A.seminorm_eq (v : E), ← A.seminorm_eq (w : E)]
    exact map_add_le_add A.seminorm (v : E) (w : E)
  norm_eq_zero_iff := A.norm_zero_iff

instance : NormedAddCommGroup A.Space := NormedAddCommGroup.ofCore (norm_core A)
instance : NormedSpace ℝ A.Space := NormedSpace.ofCore (norm_core A)

/-- The canonical wrapping map changes no vector or algebraic operation. -/
def wrap : E ≃ₗ[ℝ] A.Space := LinearEquiv.refl ℝ E

instance [FiniteDimensional ℝ E] : FiniteDimensional ℝ A.Space :=
  FiniteDimensional.of_injective A.wrap.symm.toLinearMap A.wrap.symm.injective

instance [FiniteDimensional ℝ E] : CompleteSpace A.Space := FiniteDimensional.complete ℝ A.Space

/-- The canonical topological bridge, with no assertion about the auxiliary norm. -/
def bridge [FiniteDimensional ℝ E] : E ≃L[ℝ] A.Space :=
  { A.wrap with
    continuous_toFun := A.wrap.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := A.wrap.symm.toLinearMap.continuous_of_finiteDimensional }

/-- The original linear operator, conjugated solely by the canonical wrapping map. -/
def operator [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) : A.Space →L[ℝ] A.Space :=
  LinearMap.toContinuousLinearMap (A.wrap.toLinearMap ∘ₗ H ∘ₗ A.wrap.symm.toLinearMap)



private lemma positive_bound (β : E →ₗ[ℝ] ℝ)
    (hβ : ∀ v ∈ A.cone, 0 ≤ β v) (v : E) :
    |β v| ≤ β A.unit * A.orderNorm v := by
  have hv := A.norm_attained v
  have hl := hβ _ hv.2.2
  have hu := hβ _ hv.2.1
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma positive_zero_mass (β : E →ₗ[ℝ] ℝ)
    (hβ : ∀ v ∈ A.cone, 0 ≤ β v) (hm : β A.unit = 0) : β = 0 := by
  ext v
  have h := A.positive_bound β hβ v
  rw [hm, zero_mul] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The original positive or signed functional transported to the order-norm copy. -/
def functional [FiniteDimensional ℝ E] (β : E →ₗ[ℝ] ℝ) : A.Space →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (β ∘ₗ A.wrap.symm.toLinearMap)


private lemma positive_unital_contraction (T : E →ₗ[ℝ] E)
    (hT : ∀ v ∈ A.cone, T v ∈ A.cone) (hunit : T A.unit = A.unit) (v : E) :
    A.orderNorm (T v) ≤ A.orderNorm v := by
  apply (A.norm_le_iff (T v) (A.orderNorm v)).mpr
  have hv := A.norm_attained v
  refine ⟨hv.1, ?_, ?_⟩
  · simpa only [map_sub, map_smul, hunit] using hT _ hv.2.1
  · simpa only [map_add, map_smul, hunit] using hT _ hv.2.2

private lemma positive_inverse_isometry (T : E ≃ₗ[ℝ] E)
    (hT : ∀ v ∈ A.cone, T v ∈ A.cone)
    (hTi : ∀ v ∈ A.cone, T.symm v ∈ A.cone) (hunit : T A.unit = A.unit) (v : E) :
    A.orderNorm (T v) = A.orderNorm v := by
  have hiunit : T.symm A.unit = A.unit := by
    apply T.injective
    simpa only [LinearEquiv.apply_symm_apply] using hunit.symm
  apply le_antisymm (A.positive_unital_contraction T.toLinearMap hT hunit v)
  simpa only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    A.positive_unital_contraction T.symm.toLinearMap hTi hiunit (T v)

/-- The exact nonnegative global-bound set in the original order norm. -/
def operatorBounds (H : E →ₗ[ℝ] E) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ v : E, A.orderNorm (H v) ≤ c * A.orderNorm v}



private lemma square_bound [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (v : E) :
    A.orderNorm (H (H v)) ≤ ‖A.operator H * A.operator H‖ * A.orderNorm v := by
  exact (A.operator H * A.operator H).le_opNorm (A.wrap v)

private lemma centered_bound (x : E) (hx : x ∈ A.cone) (hux : A.unit - x ∈ A.cone) :
    A.orderNorm (x - (1 / 2 : ℝ) • A.unit) ≤ 1 / 2 := by
  apply (A.norm_le_iff _ _).mpr
  refine ⟨by norm_num, ?_, ?_⟩
  · have he : (1 / 2 : ℝ) • A.unit - (x - (1 / 2 : ℝ) • A.unit) =
        A.unit - x := by module
    rw [he]
    exact hux
  · have he : (1 / 2 : ℝ) • A.unit + (x - (1 / 2 : ℝ) • A.unit) = x := by module
    rw [he]
    exact hx

/-- The exponential of the given original operator in the original finite-dimensional space. -/
def originalFlow [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  NormedSpace.exp (t • LinearMap.toContinuousLinearMap H)

private lemma flow_inverse [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (t : ℝ) (v : E) :
    originalFlow H (-t) (originalFlow H t v) = v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  let B : E →L[ℝ] E := t • LinearMap.toContinuousLinearMap H
  have h : NormedSpace.exp (-B) * NormedSpace.exp B = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl B).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have hv := congrArg (fun L : E →L[ℝ] E => L v) h
  simpa only [originalFlow, neg_smul, mul_apply_eq_comp,
    one_apply_eq_self] using hv


private lemma flow_isometry [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hflow : ∀ t : ℝ,
      (∀ v ∈ A.cone, originalFlow H t v ∈ A.cone) ∧ originalFlow H t A.unit = A.unit)
    (t : ℝ) (v : E) :
    A.orderNorm (originalFlow H t v) = A.orderNorm v := by
  let T : E ≃ₗ[ℝ] E :=
    { (originalFlow H t).toLinearMap with
      invFun := originalFlow H (-t)
      left_inv := flow_inverse H t
      right_inv := by
        intro w
        change originalFlow H t (originalFlow H (-t) w) = w
        simpa only [neg_neg] using flow_inverse H (-t) w }
  exact A.positive_inverse_isometry T (hflow t).1 (hflow (-t)).1 (hflow t).2 v

private lemma centered_orbit_bound [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hu : H A.unit = 0)
    (hflow : ∀ t : ℝ,
      (∀ v ∈ A.cone, originalFlow H t v ∈ A.cone) ∧ originalFlow H t A.unit = A.unit)
    (β : E →ₗ[ℝ] ℝ) (hβ : ∀ v ∈ A.cone, 0 ≤ β v)
    (x : E) (hx : x ∈ A.cone) (hux : A.unit - x ∈ A.cone) (t : ℝ) :
    |β (originalFlow H t (H (H x)))| ≤
      β A.unit * ‖A.operator H * A.operator H‖ / 2 := by
  let z := x - (1 / 2 : ℝ) • A.unit
  have hz : A.orderNorm z ≤ 1 / 2 := A.centered_bound x hx hux
  have hH : H (H x) = H (H z) := by
    simp only [z, map_sub, map_smul, hu, smul_zero, sub_zero]
  have hm : 0 ≤ β A.unit := hβ _ A.unit_mem
  calc
    |β (originalFlow H t (H (H x)))|
        ≤ β A.unit * A.orderNorm (originalFlow H t (H (H x))) :=
      A.positive_bound β hβ _
    _ = β A.unit * A.orderNorm (H (H z)) := by rw [A.flow_isometry H hflow, hH]
    _ ≤ β A.unit * (‖A.operator H * A.operator H‖ * A.orderNorm z) :=
      mul_le_mul_of_nonneg_left (A.square_bound H z) hm
    _ ≤ β A.unit * (‖A.operator H * A.operator H‖ * (1 / 2)) := by
      gcongr
    _ = β A.unit * ‖A.operator H * A.operator H‖ / 2 := by ring

private lemma vector_orbit_hasDerivAt [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => originalFlow H s x) (originalFlow H t (H x)) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hd := (hasDerivAt_exp_smul_const (LinearMap.toContinuousLinearMap H) t).clm_apply
    (hasDerivAt_const t x)
  simpa [originalFlow, mul_apply_eq_comp] using hd

private lemma flow_unit [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hu : H A.unit = 0) (t : ℝ) : originalFlow H t A.unit = A.unit := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => originalFlow H r A.unit) 0 s := by
    simpa [hu] using vector_orbit_hasDerivAt H A.unit s
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [originalFlow] using h

private lemma scalar_square_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hpos : ∀ t, 0 ≤ f t) (M : ℝ)
    (hsecond : ∀ t, |iteratedDeriv 2 f t| ≤ M) :
    (deriv f 0) ^ 2 ≤ 2 * M * f 0 := by
  have hpoly : ∀ s : ℝ, 0 ≤ (M / 2) * (s * s) + deriv f 0 * s + f 0 := by
    intro s
    by_cases hs : s = 0
    · simpa [hs] using hpos 0
    have hne : (0 : ℝ) ≠ s := Ne.symm hs
    obtain ⟨c, hc, he⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hf.contDiffOn
    have hd : derivWithin f (Set.uIcc 0 s) 0 = deriv f 0 :=
      (hf.differentiable (by norm_num)).differentiableAt.derivWithin
        ((uniqueDiffOn_uIcc hne) 0 (by simp))
    have ht : taylorWithinEval f 1 (Set.uIcc 0 s) 0 s = f 0 + s * deriv f 0 := by
      simp [taylorWithinEval_succ, iteratedDerivWithin_one, hd]
    rw [ht] at he
    norm_num at he
    have hb := (abs_le.mp (hsecond c)).2
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg s)
    nlinarith [hpos s]
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  nlinarith

private lemma orbit_hasDerivAt [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (β : E →ₗ[ℝ] ℝ) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => β (originalFlow H s x))
      (β (originalFlow H t (H x))) t := by
  have hd := vector_orbit_hasDerivAt H x t
  have hb : HasFDerivAt (LinearMap.toContinuousLinearMap β)
      (LinearMap.toContinuousLinearMap β)
      (originalFlow H t x) :=
    (LinearMap.toContinuousLinearMap β).hasFDerivAt
  have h := hb.comp_hasDerivAt t hd
  simpa [Function.comp_def, originalFlow, mul_apply_eq_comp] using h

private lemma orbit_contDiff [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (β : E →ₗ[ℝ] ℝ) (x : E) :
    ContDiff ℝ 2 (fun s : ℝ => β (originalFlow H s x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have he : ContDiff ℝ 2
      (fun s : ℝ => NormedSpace.exp (s • LinearMap.toContinuousLinearMap H)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    have hs : ContDiff ℝ 2 (fun r : ℝ => r • LinearMap.toContinuousLinearMap H) :=
      ((1 : ℝ →L[ℝ] ℝ).smulRight (LinearMap.toContinuousLinearMap H)).contDiff
    exact (NormedSpace.exp_analytic (s • LinearMap.toContinuousLinearMap H)).contDiffAt.comp s
      hs.contDiffAt
  exact (LinearMap.toContinuousLinearMap β).contDiff.comp (he.clm_apply contDiff_const)

private lemma reverse_certificate [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hu : H A.unit = 0)
    (hpositive : ∀ t : ℝ, ∀ v ∈ A.cone, originalFlow H t v ∈ A.cone)
    (β : E →ₗ[ℝ] ℝ) (hβ : ∀ v ∈ A.cone, 0 ≤ β v)
    (x : E) (hx : x ∈ A.cone) (hux : A.unit - x ∈ A.cone) :
    |β (H x)| ^ 2 ≤ ‖A.operator H * A.operator H‖ * β x * β A.unit := by
  have hflow (t : ℝ) :
      (∀ v ∈ A.cone, originalFlow H t v ∈ A.cone) ∧ originalFlow H t A.unit = A.unit :=
    ⟨hpositive t, A.flow_unit H hu t⟩
  let f : ℝ → ℝ := fun s => β (originalFlow H s x)
  have hd : deriv f = fun s => β (originalFlow H s (H x)) := by
    funext s
    exact (orbit_hasDerivAt H β x s).deriv
  have hdd : iteratedDeriv 2 f = fun s => β (originalFlow H s (H (H x))) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one, hd]
    funext s
    exact (orbit_hasDerivAt H β (H x) s).deriv
  have hf0 : f 0 = β x := by simp [f, originalFlow]
  have hd0 : deriv f 0 = β (H x) := by rw [hd]; simp [originalFlow]
  have hs := scalar_square_bound f (orbit_contDiff H β x)
    (fun s => hβ _ ((hflow s).1 x hx))
    (β A.unit * ‖A.operator H * A.operator H‖ / 2)
    (by intro t; rw [hdd]; exact A.centered_orbit_bound H hu hflow β hβ x hx hux t)
  rw [hf0, hd0] at hs
  rw [sq_abs]
  nlinarith


/-- The full original positive dual in its usual finite-dimensional topology. -/
def positiveDual : Set (E →L[ℝ] ℝ) := {β | ∀ v ∈ A.cone, 0 ≤ β v}

/-- A fixed coefficient on all original mathematical effects. -/
def Certificate (H : E →ₗ[ℝ] E) (K : ℝ) (β : E →L[ℝ] ℝ) : Prop :=
  ∀ x : E, x ∈ A.cone → A.unit - x ∈ A.cone →
    |β (H x)| ^ 2 ≤ K * β x * β A.unit

private lemma cone_certificate (H : E →ₗ[ℝ] E) (P : Set (E →L[ℝ] ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hP : P ⊆ A.positiveDual)
    (hcert : ∀ α ∈ P, A.Certificate H K α)
    (β : E →L[ℝ] ℝ) (hβ : β ∈ PointedCone.hull ℝ P) : A.Certificate H K β := by
  obtain ⟨c, hsupport, hc, rfl⟩ := PointedCone.mem_hull_set.mp hβ
  intro x hx hux
  have hb := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul c.support
    (r := fun α => c α * α (H x))
    (f := fun α => c α * α x)
    (g := fun α => K * c α * α A.unit)
    (fun α hα => mul_nonneg (hc α) (hP (hsupport hα) x hx))
    (fun α hα => mul_nonneg (mul_nonneg hK (hc α))
      (hP (hsupport hα) A.unit A.unit_mem))
    (by
      intro α hα
      have ha := hcert α (hsupport hα) x hx hux
      rw [sq_abs] at ha
      have ht := mul_le_mul_of_nonneg_left ha (sq_nonneg (c α))
      nlinarith only [ht])
  simp only [Finsupp.sum, sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [sq_abs]
  simp only [mul_assoc, ← Finset.mul_sum] at hb
  nlinarith only [hb]

private lemma closure_certificate (H : E →ₗ[ℝ] E) (P : Set (E →L[ℝ] ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hP : P ⊆ A.positiveDual)
    (hcert : ∀ α ∈ P, A.Certificate H K α)
    (β : E →L[ℝ] ℝ) (hβ : β ∈ closure (PointedCone.hull ℝ P : Set (E →L[ℝ] ℝ))) :
    A.Certificate H K β := by
  intro x hx hux
  have hs : IsClosed {γ : E →L[ℝ] ℝ |
      |γ (H x)| ^ 2 ≤ K * γ x * γ A.unit} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact closure_minimal
    (fun γ hγ => A.cone_certificate H P K hK hP hcert γ hγ x hx hux) hs hβ

private lemma scaled_certificate (H : E →ₗ[ℝ] E) (K : ℝ) (β : E →L[ℝ] ℝ)
    (hcert : A.Certificate H K β) (r : ℝ) (hr : 0 < r) (y : E)
    (hy : y ∈ A.cone) (hry : r • A.unit - y ∈ A.cone) :
    |β (H y)| ^ 2 ≤ K * r * β y * β A.unit := by
  let x := r⁻¹ • y
  have hx : x ∈ A.cone := A.cone.smul_mem (inv_pos.mpr hr) hy
  have hux : A.unit - x ∈ A.cone := by
    simpa [x, smul_sub, smul_smul, hr.ne'] using
      A.cone.smul_mem (inv_pos.mpr hr) hry
  have hyx : y = r • x := by simp [x, hr.ne']
  have h1 : β (H y) = r * β (H x) := by rw [hyx, map_smul, map_smul, smul_eq_mul]
  have h2 : β y = r * β x := by rw [hyx, map_smul, smul_eq_mul]
  calc
    |β (H y)| ^ 2 = r ^ 2 * |β (H x)| ^ 2 := by rw [h1, abs_mul, mul_pow, sq_abs]
    _ ≤ r ^ 2 * (K * β x * β A.unit) :=
      mul_le_mul_of_nonneg_left (hcert x hx hux) (sq_nonneg r)
    _ = K * r * β y * β A.unit := by rw [h2]; ring

private lemma zero_contact (H : E →ₗ[ℝ] E) (K : ℝ) (β : E →L[ℝ] ℝ)
    (hcert : A.Certificate H K β) (y : E) (hy : y ∈ A.cone) (hzero : β y = 0) :
    β (H y) = 0 := by
  let r := A.orderNorm y + 1
  have hr : 0 < r := by dsimp [r]; linarith [A.norm_nonneg y]
  have hry : r • A.unit - y ∈ A.cone :=
    ((A.norm_le_iff y r).mp (by dsimp [r]; linarith)).2.1
  have h := A.scaled_certificate H K β hcert r hr y hy hry
  rw [hzero, mul_zero, zero_mul] at h
  exact abs_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _)))

private lemma source_certificate (H : E →ₗ[ℝ] E) (P : Set (E →L[ℝ] ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hP : P ⊆ A.positiveDual)
    (hspan : closure (PointedCone.hull ℝ P : Set (E →L[ℝ] ℝ)) = A.positiveDual)
    (hcert : ∀ α ∈ P, A.Certificate H K α) :
    (∀ β ∈ A.positiveDual, A.Certificate H K β) ∧
    (∀ β ∈ A.positiveDual, ∀ r : ℝ, 0 < r → ∀ y : E,
      y ∈ A.cone → r • A.unit - y ∈ A.cone →
      |β (H y)| ^ 2 ≤ K * r * β y * β A.unit) ∧
    (∀ β ∈ A.positiveDual, ∀ y : E, y ∈ A.cone → β y = 0 → β (H y) = 0) := by
  have hall : ∀ β ∈ A.positiveDual, A.Certificate H K β := by
    intro β hβ
    exact A.closure_certificate H P K hK hP hcert β (by rwa [hspan])
  exact ⟨hall, fun β hβ => A.scaled_certificate H K β (hall β hβ),
    fun β hβ => A.zero_contact H K β (hall β hβ)⟩

private lemma add_unit_interior (y : E) (hy : y ∈ A.cone) (ε : ℝ) (hε : 0 < ε) :
    y + ε • A.unit ∈ interior (A.cone : Set E) := by
  have hscale : ε • A.unit ∈ interior (A.cone : Set E) := by
    apply interior_mono (s := ε • (A.cone : Set E)) ?_ ?_
    · rintro v ⟨z, hz, rfl⟩
      exact A.cone.smul_mem hε hz
    · rw [interior_smul₀ hε.ne']
      exact smul_mem_smul_set A.interior_unit
  apply interior_mono (s := (A.cone : Set E) + (A.cone : Set E)) ?_ ?_
  · rintro v ⟨z, hz, w, hw, rfl⟩
    exact A.cone.add_mem hz hw
  · exact subset_interior_add_right ⟨y, hy, ε • A.unit, hscale, rfl⟩

private lemma boundary_support (z : E) (hz : z ∈ A.cone)
    (hzi : z ∉ interior (A.cone : Set E)) :
    ∃ β : E →L[ℝ] ℝ, (∀ v ∈ A.cone, 0 ≤ β v) ∧ β z = 0 ∧ 0 < β A.unit := by
  obtain ⟨f, hfne, hf⟩ := geometric_hahn_banach_of_nonempty_interior_point
    A.cone.convex hzi ⟨A.unit, A.interior_unit⟩
  have hfz : f z = 0 := by
    have h0 := hf 0 A.zero_mem
    have h2 := hf ((2 : ℝ) • z) (A.cone.smul_mem (by norm_num) hz)
    simp only [map_zero, map_smul, smul_eq_mul] at h0 h2
    linarith
  let β : E →L[ℝ] ℝ := -f
  have hβ : ∀ v ∈ A.cone, 0 ≤ β v := by
    intro v hv
    change 0 ≤ -f v
    have := hf v hv
    linarith
  refine ⟨β, hβ, by simp [β, hfz], ?_⟩
  have hmass := hβ A.unit A.unit_mem
  by_contra hnot
  have hzβ := A.positive_zero_mass β.toLinearMap hβ (le_antisymm (le_of_not_gt hnot) hmass)
  have hβ0 : β = 0 := by
    ext v
    exact congrArg (fun l : E →ₗ[ℝ] ℝ => l v) hzβ
  apply hfne
  simpa [β] using congrArg Neg.neg hβ0

private lemma perturbed_interior [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] E)
    (hcp : ∀ z ∈ A.cone, ∀ β : E →ₗ[ℝ] ℝ,
      (∀ v ∈ A.cone, 0 ≤ β v) → β z = 0 → 0 ≤ β (L z))
    (a : ℝ) (ha : a • A.unit - L A.unit - A.unit ∈ A.cone)
    (y : E) (hy : y ∈ A.cone) (ε : ℝ) (hε : 0 < ε)
    (S : ℝ) (hS : 0 ≤ S) :
    originalFlow L S y + (ε * Real.exp (a * S)) • A.unit ∈ interior (A.cone : Set E) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let d := a • A.unit - L A.unit
  let w : ℝ → E := fun t => originalFlow L t y + (ε * Real.exp (a * t)) • A.unit
  have hd (t : ℝ) : HasDerivAt w
      (L (w t) + (ε * Real.exp (a * t)) • d) t := by
    have hflow := (hasDerivAt_exp_smul_const' (LinearMap.toContinuousLinearMap L) t).clm_apply
      (hasDerivAt_const t y)
    have hflow' : HasDerivAt (fun s : ℝ => originalFlow L s y)
        (L (originalFlow L t y)) t := by
      simpa only [originalFlow, mul_apply_eq_comp, map_zero, add_zero,
        LinearMap.coe_toContinuousLinearMap'] using hflow
    have hpert := (((hasDerivAt_id t).const_mul a).exp.const_mul ε).smul_const A.unit
    have hpert' : HasDerivAt (fun s : ℝ => (ε * Real.exp (a * s)) • A.unit)
        ((ε * Real.exp (a * t) * a) • A.unit) t := by
      simpa only [id_eq, mul_one, mul_assoc] using hpert
    have he : L (w t) + (ε * Real.exp (a * t)) • d =
        L (originalFlow L t y) + (ε * Real.exp (a * t) * a) • A.unit := by
      dsimp [w, d]
      simp only [map_add, map_smul, smul_sub, smul_smul]
      module
    rw [he]
    exact hflow'.add hpert'
  have hw : Continuous w := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hw0 : w 0 ∈ interior (A.cone : Set E) := by
    simpa [w, originalFlow] using A.add_unit_interior y hy ε hε
  by_contra hbad
  let B : Set ℝ := Icc 0 S ∩ w ⁻¹' (interior (A.cone : Set E))ᶜ
  have hBc : IsCompact B :=
    isCompact_Icc.inter_right (isClosed_compl_iff.mpr isOpen_interior |>.preimage hw)
  obtain ⟨T, hT⟩ := hBc.exists_isLeast ⟨S, ⟨⟨hS, le_rfl⟩, hbad⟩⟩
  have hTpos : 0 < T := by
    apply lt_of_le_of_ne hT.1.1.1
    intro hzero
    exact hT.1.2 (hzero ▸ hw0)
  have hbefore (s : ℝ) (hs : s ∈ Ico 0 T) : w s ∈ interior (A.cone : Set E) := by
    by_contra h
    have hb : s ∈ B := ⟨⟨hs.1, hs.2.le.trans hT.1.1.2⟩, h⟩
    exact (not_le_of_gt hs.2) (hT.2 hb)
  have hwT : w T ∈ A.cone := by
    have hc : IsClosed (w ⁻¹' (A.cone : Set E)) := A.closed.preimage hw
    have hs : Ico 0 T ⊆ w ⁻¹' (A.cone : Set E) :=
      fun s hs => @interior_subset E _ (A.cone : Set E) (w s) (hbefore s hs)
    apply closure_minimal hs hc
    rw [closure_Ico hTpos.ne]
    exact ⟨hTpos.le, le_rfl⟩
  obtain ⟨β, hβ, hβz, hβu⟩ := A.boundary_support (w T) hwT hT.1.2
  have hder := β.hasFDerivAt.comp_hasDerivAt T (hd T)
  have hnonpos : β (L (w T) + (ε * Real.exp (a * T)) • d) ≤ 0 := by
    apply le_of_tendsto hder.tendsto_slope_zero_left
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hTpos)] with h hh
    have hv : 0 ≤ β (w (T + h)) :=
      hβ _ (interior_subset (hbefore (T + h) ⟨by linarith [hh.1], by linarith [hh.2]⟩))
    simp only [Function.comp_apply, hβz, sub_zero, smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hh.2.le) hv
  have hcpz := hcp (w T) hwT β.toLinearMap hβ hβz
  have hdpos : 0 < β d := by
    have := hβ (d - A.unit) ha
    simp only [map_sub] at this
    linarith
  have hεT : 0 < ε * Real.exp (a * T) := mul_pos hε (Real.exp_pos _)
  have hstrict : 0 < β (L (w T) + (ε * Real.exp (a * T)) • d) := by
    simp only [map_add, map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos hcpz (mul_pos hεT hdpos)
  exact (not_le_of_gt hstrict) hnonpos

/-- Cross-positivity on the full original algebraic positive dual preserves the
original cone under the same operator exponential for every nonnegative time.
No condition on L(u) is imposed. -/
theorem cross_positive_flow [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] E)
    (hcp : ∀ z ∈ A.cone, ∀ β : E →ₗ[ℝ] ℝ,
      (∀ v ∈ A.cone, 0 ≤ β v) → β z = 0 → 0 ≤ β (L z)) :
    ∀ t : ℝ, 0 ≤ t → ∀ y : E, y ∈ A.cone → originalFlow L t y ∈ A.cone := by
  intro t ht y hy
  let a := A.orderNorm (L A.unit) + 1
  have ha : a • A.unit - L A.unit - A.unit ∈ A.cone := by
    have h := (A.norm_attained (L A.unit)).2.1
    convert h using 1 <;> dsimp [a] <;> module
  have hw (ε : ℝ) (hε : 0 < ε) := A.perturbed_interior L hcp a ha y hy ε hε t ht
  have hlim : Tendsto
      (fun ε : ℝ => originalFlow L t y + (ε * Real.exp (a * t)) • A.unit)
      (𝓝[>] 0) (𝓝 (originalFlow L t y)) := by
    have hc : Continuous
        (fun ε : ℝ => originalFlow L t y + (ε * Real.exp (a * t)) • A.unit) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply A.closed.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact interior_subset (hw ε hε)

private lemma zero_contact_flow [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hzero : ∀ β ∈ A.positiveDual, ∀ y : E, y ∈ A.cone → β y = 0 → β (H y) = 0) :
    ∀ t : ℝ, ∀ y : E, y ∈ A.cone → originalFlow H t y ∈ A.cone := by
  have hcp : ∀ z ∈ A.cone, ∀ β : E →ₗ[ℝ] ℝ,
      (∀ v ∈ A.cone, 0 ≤ β v) → β z = 0 → 0 ≤ β (H z) := by
    intro z hz β hβ hb
    exact le_of_eq (hzero (LinearMap.toContinuousLinearMap β) hβ z hz hb).symm
  have hcm : ∀ z ∈ A.cone, ∀ β : E →ₗ[ℝ] ℝ,
      (∀ v ∈ A.cone, 0 ≤ β v) → β z = 0 → 0 ≤ β ((-H) z) := by
    intro z hz β hβ hb
    have hh := hzero (LinearMap.toContinuousLinearMap β) hβ z hz hb
    change β (H z) = 0 at hh
    simpa only [LinearMap.neg_apply, map_neg, hh, neg_zero] using (le_refl (0 : ℝ))
  intro t y hy
  by_cases ht : 0 ≤ t
  · exact A.cross_positive_flow H hcp t ht y hy
  · have hp := A.cross_positive_flow (-H) hcm (-t) (by linarith) y hy
    simpa [originalFlow, neg_smul, smul_neg] using hp

/-- The same original H satisfies the quantitative preparation criterion iff its
actual exponential is positive and unital at every real time. The original
coefficient extends unchanged to the entire positive dual and to radius r with
exact factor r; conversely the original order-norm square-operator norm works,
including the complementary-effect minimum. -/
theorem quantitative_generator_iff [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hu : H A.unit = 0) (P : Set (E →L[ℝ] ℝ))
    (hP : P ⊆ A.positiveDual)
    (hspan : closure (PointedCone.hull ℝ P : Set (E →L[ℝ] ℝ)) = A.positiveDual) :
    ((∃ K : ℝ, 0 ≤ K ∧ ∀ α ∈ P, A.Certificate H K α) ↔
      ∀ t : ℝ, (∀ y ∈ A.cone, originalFlow H t y ∈ A.cone) ∧
        originalFlow H t A.unit = A.unit) ∧
    (∀ K : ℝ, 0 ≤ K → (∀ α ∈ P, A.Certificate H K α) →
      (∀ β ∈ A.positiveDual, A.Certificate H K β) ∧
      (∀ β ∈ A.positiveDual, ∀ r : ℝ, 0 < r → ∀ y : E,
        y ∈ A.cone → r • A.unit - y ∈ A.cone →
        |β (H y)| ^ 2 ≤ K * r * β y * β A.unit)) ∧
    ((∀ t : ℝ, (∀ y ∈ A.cone, originalFlow H t y ∈ A.cone) ∧
        originalFlow H t A.unit = A.unit) →
      (∀ β ∈ A.positiveDual, A.Certificate H ‖A.operator H * A.operator H‖ β) ∧
      (∀ β ∈ A.positiveDual, ∀ x : E, x ∈ A.cone → A.unit - x ∈ A.cone →
        |β (H x)| ^ 2 ≤ ‖A.operator H * A.operator H‖ *
          min (β x) (β (A.unit - x)) * β A.unit)) := by
  have hreverse (hflow : ∀ t : ℝ, (∀ y ∈ A.cone, originalFlow H t y ∈ A.cone) ∧
      originalFlow H t A.unit = A.unit) :
      ∀ β ∈ A.positiveDual, A.Certificate H ‖A.operator H * A.operator H‖ β := by
    intro β hβ x hx hux
    exact A.reverse_certificate H hu (fun t => (hflow t).1) β.toLinearMap hβ x hx hux
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨K, hK, hc⟩
    have hs := A.source_certificate H P K hK hP hspan hc
    intro t
    exact ⟨A.zero_contact_flow H hs.2.2 t, A.flow_unit H hu t⟩
  · intro hflow
    exact ⟨‖A.operator H * A.operator H‖, _root_.norm_nonneg _,
      fun α hα => hreverse hflow α (hP hα)⟩
  · intro K hK hc
    have hs := A.source_certificate H P K hK hP hspan hc
    exact ⟨hs.1, hs.2.1⟩
  · intro hflow
    refine ⟨hreverse hflow, ?_⟩
    intro β hβ x hx hux
    have h1 := hreverse hflow β hβ x hx hux
    have h2 := hreverse hflow β hβ (A.unit - x) hux (by simpa using hx)
    have he : |β (H (A.unit - x))| ^ 2 = |β (H x)| ^ 2 := by
      simp [map_sub, hu]
    rw [he] at h2
    rcases le_total (β x) (β (A.unit - x)) with h | h
    · simpa only [min_eq_left h] using h1
    · simpa only [min_eq_right h] using h2


end Data

/-- The algebraic Archimedean order-unit assumptions on the original cone.
No closedness, topological interior or norm assumption is part of these data. -/
structure ArchimedeanData (E : Type*) [AddCommGroup E] [Module ℝ E] where
  cone : ConvexCone ℝ E
  unit : E
  zero_mem : (0 : E) ∈ cone
  salient : cone.Salient
  unit_mem : unit ∈ cone
  order_unit : ∀ v : E, ∃ r : ℝ, 0 < r ∧
    r • unit - v ∈ cone ∧ r • unit + v ∈ cone
  archimedean : ∀ v : E, (∀ ε : ℝ, 0 < ε → v + ε • unit ∈ cone) → v ∈ cone

namespace ArchimedeanData

variable (B : ArchimedeanData E)

private lemma interior_unit [FiniteDimensional ℝ E] :
    B.unit ∈ interior (B.cone : Set E) := by
  have hs : Submodule.span ℝ (B.cone : Set E) = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨r, hr, _, hp⟩ := B.order_unit v
    have hru := B.cone.smul_mem hr B.unit_mem
    have hh := (Submodule.span ℝ (B.cone : Set E)).sub_mem
      (Submodule.subset_span hp) (Submodule.subset_span hru)
    simpa only [add_sub_cancel_left] using hh
  have ha : affineSpan ℝ (B.cone : Set E) = ⊤ := by
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ B.zero_mem), hs]
    rfl
  obtain ⟨v, hv⟩ := B.cone.convex.interior_nonempty_iff_affineSpan_eq_top.mpr ha
  obtain ⟨r, hr, hm, _⟩ := B.order_unit v
  have hru : r • B.unit ∈ interior (B.cone : Set E) := by
    have hh : v + (r • B.unit - v) ∈ interior
        ((B.cone : Set E) + (B.cone : Set E)) :=
      subset_interior_add_left ⟨v, hv, r • B.unit - v, hm, rfl⟩
    have hsum : (B.cone : Set E) + (B.cone : Set E) ⊆ B.cone := by
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact B.cone.add_mem ha hb
    simpa only [add_sub_cancel] using interior_mono hsum hh
  have hscale : r⁻¹ • (r • B.unit) ∈ interior (B.cone : Set E) := by
    apply interior_mono (s := r⁻¹ • (B.cone : Set E)) ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact B.cone.smul_mem (inv_pos.mpr hr) hv
    · rw [interior_smul₀ (inv_ne_zero hr.ne')]
      exact smul_mem_smul_set hru
  simpa only [inv_smul_smul₀ hr.ne'] using hscale

private lemma closed [FiniteDimensional ℝ E] : IsClosed (B.cone : Set E) := by
  apply isClosed_of_closure_subset
  intro v hv
  apply B.archimedean v
  intro ε hε
  have heps : ε • B.unit ∈ interior (B.cone : Set E) := by
    apply interior_mono (s := ε • (B.cone : Set E)) ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact B.cone.smul_mem hε hw
    · rw [interior_smul₀ hε.ne']
      exact smul_mem_smul_set B.interior_unit
  have hh : v + ε • B.unit ∈ closure (B.cone : Set E) + interior (B.cone : Set E) :=
    ⟨v, hv, ε • B.unit, heps, rfl⟩
  rw [isOpen_interior.closure_add (B.cone : Set E)] at hh
  obtain ⟨a, ha, b, hb, he⟩ := hh
  rw [← he]
  exact B.cone.add_mem ha (interior_subset hb)

/-- The same original cone and unit, with their finite-dimensional topology
properties proved from the algebraic order-unit and Archimedean assumptions. -/
def toData [FiniteDimensional ℝ E] : Data E where
  cone := B.cone
  unit := B.unit
  zero_mem := B.zero_mem
  salient := B.salient
  closed := by exact closed B
  interior_unit := by exact interior_unit B


/-- The complete quantitative criterion for the original algebraic Archimedean
order-unit cone, with closedness and the interior-unit property derived in any
auxiliary finite-dimensional real normed topology. -/
theorem archimedean_quantitative_generator_iff [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hu : H B.unit = 0) (P : Set (E →L[ℝ] ℝ))
    (hP : P ⊆ B.toData.positiveDual)
    (hspan : closure (PointedCone.hull ℝ P : Set (E →L[ℝ] ℝ)) = B.toData.positiveDual) :
    IsClosed (B.cone : Set E) ∧ B.unit ∈ interior (B.cone : Set E) ∧
    ((∃ K : ℝ, 0 ≤ K ∧ ∀ α ∈ P, B.toData.Certificate H K α) ↔
      ∀ t : ℝ, (∀ y ∈ B.cone, Data.originalFlow H t y ∈ B.cone) ∧
        Data.originalFlow H t B.unit = B.unit) ∧
    (∀ K : ℝ, 0 ≤ K → (∀ α ∈ P, B.toData.Certificate H K α) →
      (∀ β ∈ B.toData.positiveDual, B.toData.Certificate H K β) ∧
      (∀ β ∈ B.toData.positiveDual, ∀ r : ℝ, 0 < r → ∀ y : E,
        y ∈ B.cone → r • B.unit - y ∈ B.cone →
        |β (H y)| ^ 2 ≤ K * r * β y * β B.unit)) ∧
    ((∀ t : ℝ, (∀ y ∈ B.cone, Data.originalFlow H t y ∈ B.cone) ∧
        Data.originalFlow H t B.unit = B.unit) →
      (∀ β ∈ B.toData.positiveDual,
        B.toData.Certificate H ‖B.toData.operator H * B.toData.operator H‖ β) ∧
      (∀ β ∈ B.toData.positiveDual, ∀ x : E, x ∈ B.cone → B.unit - x ∈ B.cone →
        |β (H x)| ^ 2 ≤ ‖B.toData.operator H * B.toData.operator H‖ *
          min (β x) (β (B.unit - x)) * β B.unit)) := by
  exact ⟨closed B, interior_unit B, B.toData.quantitative_generator_iff H hu P hP hspan⟩

end ArchimedeanData
end D5.S3.Topology.OrderUnitNorm
