/- GID: D5/S3/Topology/StableCategory/WeaklyContractibleFactor
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/WeaklyContractibleFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nullhomotopic finite order maps factor through contractible order complexes. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.Gluing.FiniteSubcomplexDeformationGlue
import D5.S3.Geometry.Gluing.MappedRealization
import D5.S3.Topology.StableCategory.MaximumProjectionRealization
import D5.S3.Topology.StableCategory.RealizedOrderMapHomotopy
import D5.S3.Topology.StableCategory.OrderComplexCylinderUnion
import D5.S3.Topology.StableCategory.TwoRowFenceCylinder

/-! Exact factorization of nullhomotopic finite order maps. -/

noncomputable section

open ContinuousMap Set Relation
open scoped ContinuousMap Classical
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.Geometry.FiniteConeCollapse (faceSimplex realization_mem_iff)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open D5.S3.Geometry.FiniteSubcomplexDeformationGlue (contractible_union)
open D5.S3.Geometry.MappedRealization (homeomorphMap)
open D5.S3.Topology.OrderComplexNullhomotopy
open D5.S3.Topology.RealizedOrderMapHomotopy
open D5.S3.Topology.MaximumProjectionRealization
open D5.S3.Topology.PosetMappingCylinderGlue
open D5.S3.Topology.OrderComplexCylinderUnion
open D5.S3.Topology.StableCategory.LebesgueStarAssignment (depthComplex iteratedRealization)
open D5.S3.Topology.BarycentricGraphDistance (Face)

namespace D5.S3.Topology.WeaklyContractibleFactor

open private realizedOrderHom_val from D5.S3.Topology.StableCategory.RealizedOrderMapHomotopy
open private depthFintype depthDecEq from
  D5.S3.Topology.StableCategory.LebesgueStarAssignment

private def HomotopyEquiv.replaceForward {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (f : C(X, Y)) (h : f.Homotopic e.toFun) : X ≃ₕ Y where
  toFun := f
  invFun := e.invFun
  left_inv := by
    obtain ⟨H⟩ := h
    exact (show (e.invFun.comp f).Homotopic (e.invFun.comp e.toFun) from
      ⟨(Homotopy.refl e.invFun).comp H⟩).trans e.left_inv
  right_inv := by
    obtain ⟨H⟩ := h
    exact (show (f.comp e.invFun).Homotopic (e.toFun.comp e.invFun) from
      ⟨H.compContinuousMap e.invFun⟩).trans e.right_inv

private theorem retract_comp_cylinderA {R A : Type} [PartialOrder R] [PartialOrder A]
    (u : R →o A) : (retract u).comp (cylinderA u).toOrderHom = OrderHom.id := rfl

private theorem retract_comp_cylinderR {R A : Type} [PartialOrder R] [PartialOrder A]
    (u : R →o A) : (retract u).comp (cylinderR u).toOrderHom = u := rfl

private theorem id_cylinder_le {R A : Type} [PartialOrder R] [PartialOrder A]
    (u : R →o A) : OrderHom.id ≤ (cylinderA u).toOrderHom.comp (retract u) := by
  intro x
  change A ⊕ R at x
  cases x with
  | inl a => exact le_rfl (a := cylinderA u a)
  | inr r => exact (cylinderR_le_cylinderA_iff u r (u r)).mpr le_rfl

variable {R A V : Type} [PartialOrder R] [PartialOrder A] [PartialOrder V]
    [Fintype R] [Fintype A] [Fintype V] [DecidableEq R] [DecidableEq A] [DecidableEq V]

private def cylinderEquiv (u : R →o A) (a : A) : Space (orderComplex (Cylinder u)) ≃ₕ
    Space (orderComplex A) := by
  classical
  let c := cylinderA u a
  refine
    { toFun := realizedOrderHom a (retract u)
      invFun := realizedOrderHom c (cylinderA u).toOrderHom
      left_inv := ?_
      right_inv := ?_ }
  · rw [← realizedOrderHom_comp a c, ← realizedOrderHom_id c]
    exact (homotopic_of_fence c (.rel _ _ (id_cylinder_le u))).symm
  · rw [← realizedOrderHom_comp c a, retract_comp_cylinderA, realizedOrderHom_id]

private def cylinderLowerEquiv (u : R →o A) (a : A)
    (eu : Space (orderComplex R) ≃ₕ Space (orderComplex A))
    (hu : eu.toFun = realizedOrderHom a u) : Space (orderComplex R) ≃ₕ
        Space (orderComplex (Cylinder u)) := by
  classical
  let C := cylinderEquiv u a
  let c := cylinderA u a
  let i := realizedOrderHom c (cylinderR u).toOrderHom
  let er := eu.trans C.symm
  have hcomp : C.toFun.comp i = eu.toFun := by
    calc
      C.toFun.comp i = realizedOrderHom a ((retract u).comp (cylinderR u).toOrderHom) :=
        (realizedOrderHom_comp c a (cylinderR u).toOrderHom (retract u)).symm
      _ = eu.toFun := by rw [retract_comp_cylinderR, hu]
  have T : er.toFun.Homotopic i := by
    obtain ⟨H⟩ := C.left_inv
    refine ⟨(H.compContinuousMap i).cast ?_ rfl⟩
    rw [ContinuousMap.comp_assoc, hcomp]
    rfl
  exact HomotopyEquiv.replaceForward er i T.symm

private theorem contractible_of_order_fence (v : V)
    (h : EqvGen (· ≤ ·) (OrderHom.id : V →o V) (OrderHom.const V v)) :
    ContractibleSpace (Space (orderComplex V)) := by
  have h' := homotopic_of_fence v h
  rw [realizedOrderHom_id] at h'
  apply (contractible_iff_id_nullhomotopic _).mpr
  let p := (realizedOrderHom v (OrderHom.const V v))
  let vpoint : Space (orderComplex V) := by
    refine ⟨Pi.single v 1, (realization_mem_iff _ _).mpr ⟨{v}, (orderVertex v).property, ?_⟩⟩
    refine ⟨fun x => ?_, by simp, fun x hx => ?_⟩
    · by_cases he : x = v <;> simp [Pi.single_apply, he]
    · have he : x ≠ v := by simpa using hx
      simp [Pi.single_apply, he]
  refine ⟨vpoint, ?_⟩
  have hc : p = ContinuousMap.const _ vpoint := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    funext x
    change (realizedOrderHom v (OrderHom.const V v) q).val x = vpoint.val x
    have hpoint : vpoint.val = (Pi.single v 1 : V → ℝ) := rfl
    rw [hpoint, realizedOrderHom_val]
    rw [FunOnFinite.linearMap_apply_apply]
    obtain ⟨s, hs, hq⟩ := (realization_mem_iff _ _).mp q.property
    by_cases he : x = v
    · subst x
      simpa [Pi.single_apply] using hq.2.1
    · have hz : (Finset.univ.filter (fun a : V => OrderHom.const V v a = x)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro _ _
        exact Ne.symm he
      rw [hz, Finset.sum_empty]
      simp [he]
  exact hc ▸ h'

/-- A mapping cylinder can replace its upper half by the lower common row when
its defining map is a homotopy equivalence on order complex realizations. -/
theorem contractible_glue (u : R →o A) (e : R ↪o V) (he : IsLowerSet (Set.range (e : R → V)))
    (a : A) (eu : Space (orderComplex R) ≃ₕ Space (orderComplex A))
    (hu : eu.toFun = realizedOrderHom a u) [ContractibleSpace (Space (orderComplex V))] :
    ContractibleSpace (Space (orderComplex (Glue u e he))) := by
  classical
  let A' := (orderComplex (Cylinder u)).map (inCylinder u e he)
  let B' := (orderComplex V).map (inV u e he)
  let L' := (orderComplex R).map (e.comp (inV u e he))
  obtain ⟨hUnion, hInter⟩ := orderComplex_glue u e he
  have hI : A' ⊓ B' = L' := inf_comm A' B' |>.trans hInter
  have hU : orderComplex (Glue u e he) = A' ⊔ B' := hUnion.trans (sup_comm B' A')
  let EA := homeomorphMap (orderComplex (Cylinder u)) (inCylinder u e he).toEmbedding
  let EB := homeomorphMap (orderComplex V) (inV u e he).toEmbedding
  let EL := homeomorphMap (orderComplex R) (e.comp (inV u e he)).toEmbedding
  let EI := Homeomorph.setCongr (congrArg D5.S3.Geometry.FiniteConeCollapse.realization hI)
  haveI : ContractibleSpace (Space B') := EB.symm.contractibleSpace
  let ec := cylinderLowerEquiv u a eu hu
  let E := (((EI.trans EL.symm).toHomotopyEquiv).trans ec).trans EA.toHomotopyEquiv
  have hE : E.toFun = realizationInclusion inf_le_left := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    -- The two affine maps agree because inCylinder ∘ cylinderR = inV ∘ e.
    change (EA (ec (EL.symm (EI x)))).val = x.val
    let xR := EL.symm (EI x)
    have hlabel : (inCylinder u e he : Cylinder u → Glue u e he) ∘ cylinderR u =
        (e.comp (inV u e he) : R → Glue u e he) := funext (inCylinder_cylinderR u e he)
    have hX : (EL xR).val = x.val := by
      change (EL (EL.symm (EI x))).val = x.val
      rw [EL.apply_symm_apply]
      rfl
    -- Push forward coordinates along the two equal composites.
    rw [← hX]
    change FunOnFinite.linearMap ℝ ℝ (inCylinder u e he) (ec xR).val =
      FunOnFinite.linearMap ℝ ℝ (e.comp (inV u e he)) xR.val
    rw [← hlabel, FunOnFinite.linearMap_comp]
    change _ = FunOnFinite.linearMap ℝ ℝ (inCylinder u e he)
      (FunOnFinite.linearMap ℝ ℝ (cylinderR u) xR.val)
    change FunOnFinite.linearMap ℝ ℝ (inCylinder u e he)
      (realizedOrderHom (cylinderA u a) (cylinderR u).toOrderHom xR).val = _
    rw [realizedOrderHom_val]
    rfl
  exact hU ▸ contractible_union A' B' E hE

section ExactFactor

variable {X P : Type} [PartialOrder X] [PartialOrder P]
    [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P]

/-- A finite order map with nullhomotopic realization factors as an order
embedding followed by an order map, through a finite poset with contractible
order complex. The composite agrees with the original map on every point. -/
theorem factors_through_weakly_contractible (x : X) (p : P) (f : X →o P)
    (h : (realizedOrderHom p f).Nullhomotopic) :
    ∃ (Q : Type) (ord : PartialOrder Q) (_ : Finite Q),
      letI : PartialOrder Q := ord
      ContractibleSpace (Space (orderComplex Q)) ∧
        ∃ (i : X ↪o Q) (q : Q →o P), q.comp i.toOrderHom = f := by
  classical
  obtain ⟨pt, ⟨H⟩⟩ := h
  obtain ⟨c, d, hd⟩ := order_map_fence_of_nullhomotopy p f pt H
  let R := Face (depthComplex (orderComplex X) d)
  letI : Fintype R := depthFintype (orderComplex X) (d + 1)
  letI : DecidableEq R := depthDecEq (orderComplex X) (d + 1)
  let u := maximumProjection X d
  obtain ⟨V, ord, finiteV, data⟩ :=
    TwoRowFenceCylinder.exists_extension_of_eqvGen (hd d le_rfl)
  letI : PartialOrder V := ord
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨e, ev, he, hagree, v, hv⟩ := data
  haveI : ContractibleSpace (Space (orderComplex V)) := contractible_of_order_fence v hv
  let E := ((faceOrderComplexHomeomorph (depthComplex (orderComplex X) d)).trans
    (iteratedRealization (orderComplex X) (d + 1))).toHomotopyEquiv
  let eu := HomotopyEquiv.replaceForward E (realizedOrderHom x u)
    ⟨maximumProjectionHomotopy x d⟩
  let Q := Glue u e he
  exact ⟨Q, inferInstance, inferInstance, contractible_glue u e he x eu rfl,
    inA u e he, evaluate u e he f ev hagree, evaluate_comp_inA u e he f ev hagree⟩

end ExactFactor

end D5.S3.Topology.WeaklyContractibleFactor
