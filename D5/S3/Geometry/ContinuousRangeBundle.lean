/- GID: D5/S3/Geometry/ContinuousRangeBundle
   generality: G
   mirror-B: D5/B/S3/Geometry/ContinuousRangeBundle
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Topology.VectorBundle.Basic]
   utility: none
   digest: Continuous orthogonal projections of constant finite rank give actual real range bundles. -/

import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units

/-! Local linear coordinates for actual real subspaces, with their ambient graph topology. -/


noncomputable section
open Bundle Set Filter Topology
namespace D5.S3.Geometry.ContinuousRangeBundle
variable {X E H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (S : X → Submodule ℝ H)

/-- Local coordinates are constructed from projections; they are not endpoint premises. -/
structure Chart where
  U : Set X
  open_U : IsOpen U
  forward : X → (E →L[ℝ] H)
  backward : X → (H →L[ℝ] E)
  continuousOn_forward : ContinuousOn forward U
  continuousOn_backward : ContinuousOn backward U
  mem_range : ∀ x v, forward x v ∈ S x
  left_inverse : ∀ x ∈ U, (backward x).comp (forward x) = ContinuousLinearMap.id ℝ E
  right_inverse : ∀ x ∈ U, ∀ v ∈ S x, forward x (backward x v) = v

variable {S}
/-- A continuous constant-rank projection constructs a whole neighborhood of actual linear charts. -/
theorem exists_chart (hp : Continuous (fun x => (S x).starProjection))
    (hr : ∀ x, Module.finrank ℝ (S x) = Module.finrank ℝ E) (x₀ : X) :
    ∃ a : Chart (E := E) S, x₀ ∈ a.U := by
  classical
  let e : E ≃L[ℝ] S x₀ := (LinearEquiv.ofFinrankEq E (S x₀) (hr x₀).symm).toContinuousLinearEquiv
  let A₀ : E →L[ℝ] H := (S x₀).subtypeL.comp e.toContinuousLinearMap
  let A (x : X) : E →L[ℝ] H := (S x).starProjection.comp A₀
  have hA : Continuous A := hp.clm_comp continuous_const
  have hbase : A x₀ = A₀ := by
    ext v
    exact (S x₀).starProjection_eq_self_iff.mpr (e v).property
  have hAi : Function.Injective (A x₀) := by
    rw [hbase]
    exact Subtype.val_injective.comp e.injective
  let U : Set X := {x | Function.Injective (A x)}
  have hU : IsOpen U := ContinuousLinearMap.isOpen_injective.preimage hA
  let G (x : X) := (A x).adjoint.comp (A x)
  have hG : Continuous G := by fun_prop
  have hGi (x : X) (hx : x ∈ U) : Function.Injective (G x) := by
    apply LinearMap.ker_eq_bot.mp
    exact ((A x).ker_adjoint_comp_self).trans (LinearMap.ker_eq_bot.mpr hx)
  have hGu (x : X) (hx : x ∈ U) : IsUnit (G x) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hGi x hx, (LinearMap.injective_iff_surjective (f := (G x).toLinearMap)).mp (hGi x hx)⟩
  have hGinv (x : X) (hx : x ∈ U) : (G x).IsInvertible := by
    let e := LinearEquiv.ofBijective (G x).toLinearMap
      ⟨hGi x hx, (LinearMap.injective_iff_surjective (f := (G x).toLinearMap)).mp (hGi x hx)⟩
    exact ⟨e.toContinuousLinearEquiv, rfl⟩
  let B (x : X) := (G x).inverse.comp (A x).adjoint
  have hB : ContinuousOn B U := by
    intro x hx
    have hi : ContinuousAt (fun x => (G x).inverse) x := by
      obtain ⟨v, hv⟩ := hGu x hx
      rw [← ContinuousLinearMap.ringInverse_eq_inverse]
      exact (hv ▸ NormedRing.inverse_continuousAt v).comp hG.continuousAt
    have ha : Continuous (fun x => (A x).adjoint) := by fun_prop
    exact (hi.clm_comp ha.continuousAt).continuousWithinAt
  have hleft (x : X) (hx : x ∈ U) : (B x).comp (A x) = ContinuousLinearMap.id ℝ E := by
    change ((G x).inverse.comp (A x).adjoint).comp (A x) = _
    rw [ContinuousLinearMap.comp_assoc]
    exact (hGinv x hx).inverse_comp_self
  have hrange (x : X) (hx : x ∈ U) : (A x).range = S x := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, rfl⟩
      exact (S x).starProjection_apply_mem _
    · rw [LinearMap.finrank_range_of_inj hx, hr x]
  refine ⟨⟨U, hU, A, B, hA.continuousOn, hB, ?_, hleft, ?_⟩, hAi⟩
  · intro x v
    exact (S x).starProjection_apply_mem _
  · intro x hx v hv
    obtain ⟨w, rfl⟩ := hrange x hx ▸ hv
    exact congrArg (A x) (congrArg (fun T : E →L[ℝ] E => T w) (hleft x hx))

namespace Chart
variable (a : Chart (E := E) S)
def into (x : X) : E →ₗ[ℝ] S x :=
  (a.forward x).toLinearMap.codRestrict (S x) (a.mem_range x)
def coords (x : X) : S x →ₗ[ℝ] E :=
  (a.backward x).toLinearMap.comp (S x).subtype
private theorem coords_into {x : X} (hx : x ∈ a.U) (v : E) :
    a.coords x (a.into x v) = v :=
  congrArg (fun T : E →L[ℝ] E => T v) (a.left_inverse x hx)
private theorem into_coords {x : X} (hx : x ∈ a.U) (v : S x) :
    a.into x (a.coords x v) = v :=
  Subtype.ext (a.right_inverse x hx v v.property)
def equiv {x : X} (hx : x ∈ a.U) : S x ≃ₗ[ℝ] E :=
  { a.coords x with
    invFun := a.into x
    left_inv := a.into_coords hx
    right_inv := a.coords_into hx }
def pretrivialization : Pretrivialization E (π E (fun x => ↥(S x))) where
  toFun z := (z.proj, a.coords z.proj z.2)
  invFun z := ⟨z.1, a.into z.1 z.2⟩
  source := (π E (fun x => ↥(S x))) ⁻¹' a.U
  target := a.U ×ˢ univ
  map_source' _ hz := ⟨hz, mem_univ _⟩
  map_target' _ hz := hz.1
  left_inv' z hz := by
    change TotalSpace.mk z.proj (a.into z.proj (a.coords z.proj z.2)) = z
    rw [a.into_coords hz]
  right_inv' z hz := by
    change (z.1, a.coords z.1 (a.into z.1 z.2)) = z
    rw [a.coords_into hz.1]
  open_target := a.open_U.prod isOpen_univ
  baseSet := a.U
  open_baseSet := a.open_U
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun _ _ => rfl
instance : a.pretrivialization.IsLinear ℝ where
  linear x _ := (a.coords x).isLinear
private theorem symm_eq {x : X} (hx : x ∈ a.U) (v : E) :
    a.pretrivialization.symm x v = a.into x v := by
  apply (a.equiv hx).injective
  change a.coords x (a.pretrivialization.symm x v) = a.coords x (a.into x v)
  rw [a.coords_into hx]
  exact congrArg Prod.snd (a.pretrivialization.apply_mk_symm hx v)
private theorem inducing {x : X} (hx : x ∈ a.U) :
    IsInducing (a.pretrivialization ∘ TotalSpace.mk x) :=
  isInducing_const_prod.mpr (a.equiv hx).toContinuousLinearEquiv.toHomeomorph.isInducing
end Chart

/-- A canonical atlas on the actual submodules; its transition maps use the actual inclusions. -/
def prebundle (hp : Continuous (fun x => (S x).starProjection))
    (hr : ∀ x, Module.finrank ℝ (S x) = Module.finrank ℝ E) :
    VectorPrebundle ℝ E (fun x => ↥(S x)) where
  pretrivializationAtlas := Set.range (Chart.pretrivialization (E := E) (S := S))
  pretrivialization_linear' := by rintro _ ⟨a, rfl⟩; infer_instance
  pretrivializationAt x := (exists_chart hp hr x).choose.pretrivialization
  mem_base_pretrivializationAt x := (exists_chart hp hr x).choose_spec
  pretrivialization_mem_atlas x := ⟨(exists_chart hp hr x).choose, rfl⟩
  exists_coordChange := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨fun x => (b.backward x).comp (a.forward x), ?_, ?_⟩
    · exact (b.continuousOn_backward.mono inter_subset_right).clm_comp
        (a.continuousOn_forward.mono inter_subset_left)
    · intro x hx v
      rw [a.symm_eq hx.1]
      rfl
  totalSpaceMk_isInducing x :=
    (exists_chart hp hr x).choose.inducing (exists_chart hp hr x).choose_spec
/-- The actual inclusion of the dependent range into the original product. -/
def ambient (S : X → Submodule ℝ H) (z : TotalSpace E (fun x => ↥(S x))) : X × H :=
  (z.proj, z.2.1)
abbrev RangeGraph (S : X → Submodule ℝ H) := {z : X × H // z.2 ∈ S z.1}

/-- The bundle topology is exactly the range graph topology inherited from X × H. -/
theorem topology_eq_induced (hp : Continuous (fun x => (S x).starProjection))
    (hr : ∀ x, Module.finrank ℝ (S x) = Module.finrank ℝ E) :
    (prebundle hp hr).totalSpaceTopology =
      TopologicalSpace.induced (ambient (E := E) S) inferInstance := by
  let a := prebundle hp hr
  letI := a.totalSpaceTopology
  letI := a.toFiberBundle
  have hout : Continuous (ambient (E := E) S) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    let c := (exists_chart hp hr z.proj).choose
    have hz : z.proj ∈ c.U := (exists_chart hp hr z.proj).choose_spec
    have hb : ContinuousAt (fun w : TotalSpace E (fun x => ↥(S x)) => w.proj) z :=
      (FiberBundle.continuous_proj E (fun x => ↥(S x))).continuousAt
    have hcoord : ContinuousAt (fun w : TotalSpace E (fun x => ↥(S x)) =>
        c.coords w.proj w.2) z :=
      ((FiberBundle.continuousAt_totalSpace E id).mp continuousAt_id).2
    have hf := ((c.continuousOn_forward.continuousAt (c.open_U.mem_nhds hz)).comp hb).clm_apply hcoord
    have hv : ContinuousAt (fun w : TotalSpace E (fun x => ↥(S x)) => (w.2 : H)) z := by
      apply hf.congr_of_eventuallyEq
      filter_upwards [hb.preimage_mem_nhds (c.open_U.mem_nhds hz)] with w hw
      exact (c.right_inverse w.proj hw w.2 w.2.property).symm
    exact hb.prodMk hv
  have hin : Continuous (fun z : RangeGraph S =>
      (⟨z.1.1, ⟨z.1.2, z.2⟩⟩ : TotalSpace E (fun x => ↥(S x)))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (FiberBundle.continuousAt_totalSpace E _).mpr
    have hb : ContinuousAt (fun w : RangeGraph S => w.1.1) z :=
      (continuous_fst.comp continuous_subtype_val).continuousAt
    refine ⟨hb, ?_⟩
    let c := (exists_chart hp hr z.1.1).choose
    have hz : z.1.1 ∈ c.U := (exists_chart hp hr z.1.1).choose_spec
    change ContinuousAt (fun w : RangeGraph S => c.backward w.1.1 w.1.2) z
    have hback : ContinuousAt (fun w : RangeGraph S => c.backward w.1.1) z :=
      ContinuousAt.comp (f := fun w : RangeGraph S => w.1.1) (x := z)
        (c.continuousOn_backward.continuousAt (c.open_U.mem_nhds hz)) hb
    have hv : ContinuousAt (fun w : RangeGraph S => w.1.2) z :=
      (continuous_snd.comp continuous_subtype_val).continuousAt
    exact hback.clm_apply hv
  let f : TotalSpace E (fun x => ↥(S x)) ≃ₜ RangeGraph S := {
    toFun z := ⟨ambient S z, z.2.property⟩
    invFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := hout.subtype_mk _
    continuous_invFun := hin }
  exact (IsEmbedding.subtypeVal.comp f.isEmbedding).isInducing.eq_induced

end D5.S3.Geometry.ContinuousRangeBundle
