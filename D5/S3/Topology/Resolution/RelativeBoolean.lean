/- GID: D5/S3/Topology/Resolution/RelativeBoolean
   generality: G
   mirror-B: D5/B/S3/Topology/Resolution/RelativeBoolean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual boundary-avoiding graph closure resolves compact pairs functorially. -/

import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Clopen
import Mathlib.Tactic

/-!
# Relative Boolean graph resolution

The index consists of actual subsets whose ambient frontiers avoid `C`.
The space is the closure of the actual evaluation graph. The underlying
compactification is the classical Stone/Banaschewski compactification of the
Michael modification; no novelty of that compactification is claimed.

-/

open Set Function Filter Topology TopologicalSpace
open scoped Topology

namespace D5.S3.Topology.Resolution.RelativeBoolean

universe u v w

variable {X : Type u} {X' : Type v} {X'' : Type w}
variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']

/-- An actual ambient subset, locally constant at every point of `C`. -/
def Observation (C : Set X) := {A : Set X // ∀ x ∈ C, x ∉ frontier A}

namespace Observation

/-- Complement is needed for the two possible values of a coordinate. -/
def compl {C : Set X} (A : Observation C) : Observation C :=
  ⟨A.valᶜ, by simpa only [frontier_compl] using A.property⟩

/-- Continuous inverse image preserves the actual admissible subsets. -/
def pullback {C : Set X} {C' : Set X'} (h : X → X')
    (hh : Continuous h) (hC : MapsTo h C C') (A : Observation C') : Observation C :=
  ⟨h ⁻¹' A.val, fun x hx hfront =>
    A.property (h x) (hC hx) (hh.frontier_preimage_subset A.val hfront)⟩

end Observation

abbrev Cube (C : Set X) := Observation C → Bool

noncomputable def evaluation (C : Set X) (x : X) : Cube C :=
  fun A => A.val.boolIndicator x

noncomputable def graph (C : Set X) (x : X) : X × Cube C :=
  (x, evaluation C x)

/-- The object is this graph closure, with no supplied resolution axioms. -/
def carrier (C : Set X) : Set (X × Cube C) := closure (range (graph C))

abbrev Space (C : Set X) := ↥(carrier C)

noncomputable def point (C : Set X) (x : X) : Space C :=
  ⟨graph C x, subset_closure (mem_range_self x)⟩

def projection (C : Set X) (y : Space C) : X := y.val.1

def coordinates (C : Set X) (y : Space C) : Cube C := y.val.2

theorem continuous_projection (C : Set X) : Continuous (projection C) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_coordinates (C : Set X) : Continuous (coordinates C) :=
  continuous_snd.comp continuous_subtype_val

theorem projection_surjective (C : Set X) : Surjective (projection C) :=
  fun x => ⟨point C x, rfl⟩

instance space_compact (C : Set X) [CompactSpace X] : CompactSpace (Space C) :=
  isCompact_iff_compactSpace.mp (isClosed_closure.isCompact)

instance space_hausdorff (C : Set X) [T2Space X] : T2Space (Space C) :=
  inferInstanceAs (T2Space ↥(closure (range (graph C))))

/-- Each binary coordinate constrains the first coordinate to the closure of
the corresponding actual evaluation fiber. -/
private theorem forced_coordinate (C : Set X) (y : Space C)
    (A : Observation C) (b : Bool) (hy : coordinates C y A = b) :
    projection C y ∈ closure (A.val.boolIndicator ⁻¹' {b}) := by
  let K : Set (X × Cube C) :=
    (Prod.fst ⁻¹' closure (A.val.boolIndicator ⁻¹' {b})) ∪
      ((fun z : X × Cube C => z.2 A) ⁻¹' ({b} : Set Bool)ᶜ)
  have hK : IsClosed K :=
    (isClosed_closure.preimage continuous_fst).union
      ((isClosed_discrete _).preimage ((continuous_apply A).comp continuous_snd))
  have hgraph : range (graph C) ⊆ K := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : A.val.boolIndicator x = b
    · exact Or.inl (subset_closure hx)
    · exact Or.inr hx
  have hm : y.val ∈ K := closure_minimal hgraph hK y.property
  rcases hm with hm | hm
  · exact hm
  · exact False.elim (hm hy)

theorem mem_closure_of_coordinate_true (C : Set X) (y : Space C)
    (A : Observation C) (hy : coordinates C y A = true) :
    projection C y ∈ closure A.val := by
  simpa only [preimage_boolIndicator_true] using forced_coordinate C y A true hy

theorem mem_closure_compl_of_coordinate_false (C : Set X) (y : Space C)
    (A : Observation C) (hy : coordinates C y A = false) :
    projection C y ∈ closure A.valᶜ := by
  simpa only [preimage_boolIndicator_false] using forced_coordinate C y A false hy

private theorem coordinate_true_of_interior (C : Set X) (y : Space C)
    (A : Observation C) (hy : projection C y ∈ interior A.val) :
    coordinates C y A = true := by
  cases hb : coordinates C y A with
  | false =>
    have hc := mem_closure_compl_of_coordinate_false C y A hb
    rw [closure_compl] at hc
    exact False.elim (hc hy)
  | true => rfl

private theorem coordinate_false_of_interior_compl (C : Set X) (y : Space C)
    (A : Observation C) (hy : projection C y ∈ interior A.valᶜ) :
    coordinates C y A = false := by
  cases hb : coordinates C y A with
  | false => rfl
  | true =>
    have hc := mem_closure_of_coordinate_true C y A hb
    rw [interior_compl] at hy
    exact False.elim (hy hc)

/-- The full boundary-avoiding neighborhood lemma, including points off `C`. -/
theorem exists_open_closure_subset_avoiding_frontier
    [CompactSpace X] [T2Space X] {C : Set X} (hC : IsClosed C)
    [TotallyDisconnectedSpace C] {U : Set X} (hU : IsOpen U)
    {x : X} (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
      (∀ c ∈ C, c ∉ frontier V) := by
  classical
  by_cases hxc : x ∈ C
  · let : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
    obtain ⟨D, hD, hxD, hDU⟩ :=
      compact_exists_isClopen_in_isOpen
        (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : C → X)))
        (show (⟨x, hxc⟩ : C) ∈ (Subtype.val : C → X) ⁻¹' U from hx)
    let K : Set X := (Subtype.val : C → X) '' D
    let L : Set X := (Subtype.val : C → X) '' Dᶜ
    have hK : IsClosed K := (hD.isClosed.isCompact.image continuous_subtype_val).isClosed
    have hL : IsClosed L := (hD.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
    have hKU : K ⊆ U \ L := by
      rintro _ ⟨c, hc, rfl⟩
      refine ⟨hDU hc, ?_⟩
      rintro ⟨d, hd, heq⟩
      have hdc : d = c := Subtype.ext heq
      exact hd (hdc.symm ▸ hc)
    obtain ⟨V, hV, hKV, hVU⟩ :=
      normal_exists_closure_subset hK (hU.sdiff hL) hKU
    refine ⟨V, hV, hKV ⟨⟨x, hxc⟩, hxD, rfl⟩,
      fun z hz => (hVU hz).1, ?_⟩
    intro c hc hfront
    by_cases hcD : (⟨c, hc⟩ : C) ∈ D
    · have hcV : c ∈ V := hKV ⟨⟨c, hc⟩, hcD, rfl⟩
      rw [hV.frontier_eq] at hfront
      exact hfront.2 hcV
    · exact (hVU (frontier_subset_closure hfront)).2 ⟨⟨c, hc⟩, hcD, rfl⟩
  · obtain ⟨V, hV, hxV, hVU⟩ :=
      normal_exists_closure_subset (isClosed_singleton : IsClosed ({x} : Set X))
        (hU.sdiff hC) (by simpa only [singleton_subset_iff, Set.mem_sdiff] using And.intro hx hxc)
    refine ⟨V, hV, hxV (by simp), fun z hz => (hVU hz).1, ?_⟩
    intro c hc hfront
    exact (hVU (frontier_subset_closure hfront)).2 hc

/-- Separation of first coordinates makes the cube projection injective. -/
theorem coordinates_injective [CompactSpace X] [T2Space X]
    {C : Set X} (hC : IsClosed C) [TotallyDisconnectedSpace C] :
    Injective (coordinates C) := by
  intro y z hyz
  have hbase : projection C y = projection C z := by
    by_contra hne
    let U : Set X := {projection C z}ᶜ
    obtain ⟨V, hV, hyV, hVU, hVC⟩ :=
      exists_open_closure_subset_avoiding_frontier hC
        (isClosed_singleton.isOpen_compl : IsOpen U)
        (show projection C y ∈ U from hne)
    let A : Observation C := ⟨V, hVC⟩
    have hyone : coordinates C y A = true :=
      coordinate_true_of_interior C y A (by
        change projection C y ∈ interior V
        rwa [hV.interior_eq])
    have hzone : coordinates C z A = true := by rw [← hyz]; exact hyone
    have hzcl : projection C z ∈ closure V := mem_closure_of_coordinate_true C z A hzone
    exact hVU hzcl rfl
  apply Subtype.ext
  exact Prod.ext hbase hyz

/-- Compactness is used only after the actual separation proof. -/
theorem coordinates_is_closed_embedding [CompactSpace X] [T2Space X]
    {C : Set X} (hC : IsClosed C) [TotallyDisconnectedSpace C] :
    IsClosedEmbedding (coordinates C) :=
  (continuous_coordinates C).isClosedEmbedding (coordinates_injective hC)

theorem space_totally_disconnected [CompactSpace X] [T2Space X]
    {C : Set X} (hC : IsClosed C) [TotallyDisconnectedSpace C] :
    TotallyDisconnectedSpace (Space C) :=
  (coordinates_is_closed_embedding hC).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

private theorem mem_interior_at_core {C : Set X} (A : Observation C)
    {c : X} (hc : c ∈ C) (hA : c ∈ A.val) : c ∈ interior A.val :=
  (mem_interior_iff_notMem_frontier hA).2 (A.property c hc)

/-- Every coordinate is forced at every distinguished point. -/
theorem coordinates_eq_evaluation_at_core {C : Set X} (y : Space C)
    (hy : projection C y ∈ C) :
    coordinates C y = evaluation C (projection C y) := by
  classical
  funext A
  by_cases hA : projection C y ∈ A.val
  · exact (coordinate_true_of_interior C y A (mem_interior_at_core A hy hA)).trans
      ((A.val.mem_iff_boolIndicator _).mp hA).symm
  · have hAc : projection C y ∈ interior A.valᶜ :=
      mem_interior_at_core A.compl hy hA
    exact (coordinate_false_of_interior_compl C y A hAc).trans
      ((A.val.notMem_iff_boolIndicator _).mp hA).symm

theorem eq_point_of_projection_mem {C : Set X} (y : Space C)
    (hy : projection C y ∈ C) : y = point C (projection C y) := by
  apply Subtype.ext
  exact Prod.ext rfl (coordinates_eq_evaluation_at_core y hy)

/-- Singleton fibers hold without assuming invertibility or onto dynamics. -/
theorem fiber_singleton {C : Set X} {c : X} (hc : c ∈ C) :
    projection C ⁻¹' {c} = {point C c} := by
  ext y
  constructor
  · intro hy
    have hyc : projection C y = c := hy
    have h := eq_point_of_projection_mem y (by simpa only [hyc] using hc)
    simpa only [hyc, mem_singleton_iff] using h
  · rintro (rfl : y = point C c)
    rfl

noncomputable def sectionC (C : Set X) (c : C) : Space C := point C c.val

private theorem trace_is_clopen {C : Set X} (A : Observation C) :
    IsClopen ((Subtype.val : C → X) ⁻¹' A.val) := by
  have hopen (B : Observation C) : IsOpen ((Subtype.val : C → X) ⁻¹' B.val) := by
    have heq : (Subtype.val : C → X) ⁻¹' B.val =
        (Subtype.val : C → X) ⁻¹' interior B.val := by
      ext c
      exact ⟨fun h => mem_interior_at_core B c.property h,
        fun h => (interior_subset : interior B.val ⊆ B.val) h⟩
    rw [heq]
    exact isOpen_interior.preimage continuous_subtype_val
  exact ⟨isOpen_compl_iff.mp (hopen A.compl), hopen A⟩

theorem continuous_section (C : Set X) : Continuous (sectionC C) := by
  have he : Continuous (fun c : C => evaluation C c.val) := by
    apply continuous_pi
    intro A
    change Continuous (((Subtype.val : C → X) ⁻¹' A.val).boolIndicator)
    exact (continuous_boolIndicator_iff_isClopen _).2 (trace_is_clopen A)
  exact (continuous_subtype_val.prodMk he).subtype_mk _

/-- The distinguished subspace is homeomorphic to its full inverse image. -/
noncomputable def coreHomeomorph (C : Set X) : C ≃ₜ {y : Space C // projection C y ∈ C} where
  toFun c := ⟨sectionC C c, c.property⟩
  invFun y := ⟨projection C y.val, y.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv y := Subtype.ext (eq_point_of_projection_mem y.val y.property).symm
  continuous_toFun := (continuous_section C).subtype_mk _
  continuous_invFun := ((continuous_projection C).comp continuous_subtype_val).subtype_mk _

section Functoriality

variable {C : Set X} {C' : Set X'} {C'' : Set X''}

noncomputable def ambientMap (h : X → X') (hh : Continuous h) (hC : MapsTo h C C')
    (z : X × Cube C) : X' × Cube C' :=
  (h z.1, fun A => z.2 (Observation.pullback h hh hC A))

theorem continuous_ambient_map (h : X → X') (hh : Continuous h) (hC : MapsTo h C C') :
    Continuous (ambientMap h hh hC) :=
  (hh.comp continuous_fst).prodMk
    (continuous_pi fun A => (continuous_apply (Observation.pullback h hh hC A)).comp continuous_snd)

private theorem ambient_map_graph (h : X → X') (hh : Continuous h)
    (hC : MapsTo h C C') (x : X) :
    ambientMap h hh hC (graph C x) = graph C' (h x) := rfl

private theorem ambient_map_mem (h : X → X') (hh : Continuous h)
    (hC : MapsTo h C C') (y : Space C) : ambientMap h hh hC y.val ∈ carrier C' := by
  have hg : MapsTo (ambientMap h hh hC) (range (graph C)) (range (graph C')) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨h x, (ambient_map_graph h hh hC x).symm⟩
  exact hg.closure (continuous_ambient_map h hh hC) y.property

/-- The actual restricted map on graph closures; no extension is postulated. -/
noncomputable def lift (h : X → X') (hh : Continuous h) (hC : MapsTo h C C')
    (y : Space C) : Space C' :=
  ⟨ambientMap h hh hC y.val, ambient_map_mem h hh hC y⟩

theorem continuous_lift (h : X → X') (hh : Continuous h) (hC : MapsTo h C C') :
    Continuous (lift h hh hC) :=
  ((continuous_ambient_map h hh hC).comp continuous_subtype_val).subtype_mk _

theorem projection_lift (h : X → X') (hh : Continuous h) (hC : MapsTo h C C')
    (y : Space C) : projection C' (lift h hh hC y) = h (projection C y) := rfl

theorem lift_point (h : X → X') (hh : Continuous h) (hC : MapsTo h C C') (x : X) :
    lift h hh hC (point C x) = point C' (h x) :=
  Subtype.ext (ambient_map_graph h hh hC x)

theorem lift_id : lift (id : X → X) continuous_id (fun _ hx => hx : MapsTo id C C) = id := by
  funext y
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext A
    change y.val.2 (Observation.pullback id continuous_id (fun _ hx => hx) A) = y.val.2 A
    exact congrArg y.val.2 (Subtype.ext (by rfl))

theorem lift_comp (h : X → X') (hh : Continuous h) (hC : MapsTo h C C')
    (k : X' → X'') (hk : Continuous k) (kC : MapsTo k C' C'') :
    lift (k ∘ h) (hk.comp hh) (kC.comp hC) = lift k hk kC ∘ lift h hh hC := by
  funext y
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext A
    change y.val.2 (Observation.pullback (k ∘ h) (hk.comp hh) (kC.comp hC) A) =
      y.val.2 (Observation.pullback h hh hC (Observation.pullback k hk kC A))
    exact congrArg y.val.2 (Subtype.ext (by rfl))

/-- The same graph closure is a compact Hausdorff zero-dimensional resolution,
with continuous surjective projection and coherent lifts of arbitrary maps of
pairs. Only the source pair needs the compact resolution hypotheses. -/
theorem functorial_resolution [CompactSpace X] [T2Space X]
    (hclosed : IsClosed C) [TotallyDisconnectedSpace C]
    (h : X → X') (hh : Continuous h) (hC : MapsTo h C C')
    (k : X' → X'') (hk : Continuous k) (kC : MapsTo k C' C'') :
    CompactSpace (Space C) ∧ T2Space (Space C) ∧
      IsTopologicalBasis {U : Set (Space C) | IsClopen U} ∧
      Continuous (projection C) ∧ Surjective (projection C) ∧
      Continuous (lift h hh hC) ∧
      lift (id : X → X) continuous_id (mapsTo_id C) = id ∧
      lift (k ∘ h) (hk.comp hh) (kC.comp hC) = lift k hk kC ∘ lift h hh hC := by
  let := space_totally_disconnected hclosed
  exact ⟨inferInstance, inferInstance, isTopologicalBasis_isClopen,
    continuous_projection C, projection_surjective C, continuous_lift h hh hC,
    lift_id, lift_comp h hh hC k hk kC⟩

end Functoriality

end D5.S3.Topology.Resolution.RelativeBoolean
