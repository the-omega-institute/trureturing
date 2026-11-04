/- GID: D5/S3/Topology/OrderUnitNorm
   generality: G
   mirror-B: D5/B/S3/Topology/OrderUnitNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Gauge, mathlib/module/Mathlib.Topology.Algebra.Module.FiniteDimension]
   utility: none
   digest: The original closed salient cone and interior unit determine an attained order norm and exact operator bounds. -/

module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Geometry.Convex.Cone.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
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

private lemma interval_zero : (0 : E) ∈ A.interval := by
  simpa [interval] using And.intro A.unit_mem A.unit_mem

private lemma interval_closed : IsClosed A.interval := by
  exact (A.closed.preimage (continuous_const.sub continuous_id)).inter
    (A.closed.preimage (continuous_const.add continuous_id))

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
    change 0 ≤ A.orderNorm v ∧ A.orderNorm v • A.unit - v ∈ A.cone ∧ A.orderNorm v • A.unit + v ∈ A.cone at hv
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
@[reducible] def Space (_A : Data E) := E

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

private lemma norm_wrap (v : E) : ‖A.wrap v‖ = A.orderNorm v := rfl

private lemma unit_ball (v : E) : ‖A.wrap v‖ ≤ 1 ↔ v ∈ A.interval := by
  rw [A.norm_wrap, A.norm_le_iff]
  simp [radii, interval]

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

private lemma positive_norm [FiniteDimensional ℝ E] (β : E →ₗ[ℝ] ℝ)
    (hβ : ∀ v ∈ A.cone, 0 ≤ β v) : ‖A.functional β‖ = β A.unit := by
  have hm : 0 ≤ β A.unit := hβ _ A.unit_mem
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ hm
    intro v
    change |β (A.wrap.symm v)| ≤ β A.unit * A.orderNorm (A.wrap.symm v)
    exact A.positive_bound β hβ _
  · have hu : ‖A.wrap A.unit‖ ≤ 1 := by
      apply (A.unit_ball A.unit).mpr
      constructor
      · simpa using A.zero_mem
      · exact A.cone.add_mem A.unit_mem A.unit_mem
    have hb := (A.functional β).le_opNorm_of_le hu
    simpa only [functional, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
      LinearEquiv.symm_apply_apply, Real.norm_eq_abs, abs_of_nonneg hm, mul_one] using hb

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

private lemma operator_norm [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) :
    ‖A.operator H‖ = sInf (A.operatorBounds H) := by
  rw [ContinuousLinearMap.norm_def]
  rfl

private lemma operator_square [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) :
    A.operator H * A.operator H = A.operator (H * H) := by
  ext v
  rfl

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
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let B : E →L[ℝ] E := t • LinearMap.toContinuousLinearMap H
  have h : NormedSpace.exp (-B) * NormedSpace.exp B = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl B).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have hv := congrArg (fun L : E →L[ℝ] E => L v) h
  simpa only [originalFlow, neg_smul, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.one_apply] using hv

private lemma flow_transport [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (t : ℝ) (v : E) :
    NormedSpace.exp (t • A.operator H) (A.wrap v) =
      A.wrap (originalFlow H t v) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let J := A.bridge.conjContinuousAlgEquiv
  have hmap : J (t • LinearMap.toContinuousLinearMap H) = t • A.operator H := by
    ext w
    rfl
  have h := NormedSpace.map_exp J J.continuous (t • LinearMap.toContinuousLinearMap H)
  rw [hmap] at h
  have hv := congrArg (fun L : A.Space →L[ℝ] A.Space => L (A.wrap v)) h
  simpa only [J, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    bridge, ContinuousLinearEquiv.coe_mk', LinearEquiv.symm_apply_apply, originalFlow] using hv.symm

private lemma flow_isometry [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hflow : ∀ t : ℝ,
      (∀ v ∈ A.cone, originalFlow H t v ∈ A.cone) ∧ originalFlow H t A.unit = A.unit)
    (t : ℝ) (v : E) :
    A.orderNorm (originalFlow H t v) = A.orderNorm v := by
  let T : E ≃ₗ[ℝ] E :=
    { (originalFlow H t).toLinearMap with
      invFun := originalFlow H (-t)
      left_inv := flow_inverse H t
      right_inv := by intro w; simpa only [neg_neg] using flow_inverse H (-t) w }
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

end Data
end D5.S3.Topology.OrderUnitNorm
