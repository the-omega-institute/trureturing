/- GID: D5/S3/Topology/OrderUnitNorm
   generality: G
   mirror-B: D5/B/S3/Topology/OrderUnitNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Gauge, mathlib/module/Mathlib.Topology.Algebra.Module.FiniteDimension]
   utility: none
   digest: The original closed salient cone and interior unit determine an attained order norm and exact operator bounds. -/

import Mathlib.Analysis.Convex.Gauge
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

noncomputable section

namespace D5.S3.Topology.OrderUnitNorm

open Set Filter
open scoped Pointwise Topology

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
  · convert A.cone.convex hx.1 hy.1 ha hb hab using 1 <;> module
  · convert A.cone.convex hx.2 hy.2 ha hb hab using 1 <;> module

private lemma interval_balanced : Balanced ℝ A.interval := by
  apply (balanced_iff_neg_mem A.interval_convex).2
  intro x hx
  simpa [interval] using And.intro hx.2 hx.1

private lemma interval_nhds : A.interval ∈ 𝓝 (0 : E) := by
  have hu := mem_interior_iff_mem_nhds.mp A.interior_unit
  have hm : Tendsto (fun v : E => A.unit - v) (𝓝 0) (𝓝 A.unit) := by
    simpa using (continuous_const.sub continuous_id).tendsto (0 : E)
  have hp : Tendsto (fun v : E => A.unit + v) (𝓝 0) (𝓝 A.unit) := by
    simpa using (continuous_const.add continuous_id).tendsto (0 : E)
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
  · convert A.cone.add_mem hr.2.1 hd using 1 <;> module
  · convert A.cone.add_mem hr.2.2 hd using 1 <;> module

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
def Space := E

instance : AddCommGroup A.Space := inferInstanceAs (AddCommGroup E)
instance : Module ℝ A.Space := inferInstanceAs (Module ℝ E)
instance : Norm A.Space := ⟨fun v => A.orderNorm v⟩

private def normCore : NormedSpace.Core ℝ A.Space where
  norm_nonneg := A.norm_nonneg
  norm_smul r v := by
    change A.orderNorm (r • v) = ‖r‖ * A.orderNorm v
    simp only [← A.seminorm_eq, map_smul_eq_mul]
  norm_triangle v w := by
    change A.orderNorm (v + w) ≤ A.orderNorm v + A.orderNorm w
    simpa only [← A.seminorm_eq] using (map_add_le_add A.seminorm v w)
  norm_eq_zero_iff := A.norm_zero_iff

instance : NormedAddCommGroup A.Space := NormedAddCommGroup.ofCore A.normCore
instance : NormedSpace ℝ A.Space := NormedSpace.ofCore A.normCore

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

end Data
end D5.S3.Topology.OrderUnitNorm
