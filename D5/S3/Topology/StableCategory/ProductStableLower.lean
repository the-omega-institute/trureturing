/- GID: D5/S3/Topology/StableCategory/ProductStableLower
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/ProductStableLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The seven-triangle face-poset product needs two categorical pieces at every depth. -/

import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fintype.Powerset
import D5.S3.Topology.StableCategory.ProductStableCover
import D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer

/-!
# The all-depth lower bound for the seven-triangle product

The factor retracts from the product by the section of first projection through
a fixed face. Nonempty finite chains preserve this retraction at every depth.
A hypothetical contraction of the factor at depth `r` induces a contraction of
the face poset of `sd^(r+1) P`. Choosing a vertex in each singleton image
converts that fence to a contiguity chain in `sd^(r+1) P`. Restriction to the
boundary at the same depth forces the chain to fix the distinct vertices 1 and 2.

The one-step fence lift is the order-complex argument of Barmak–Minian,
Proposition 4.11 (https://arxiv.org/abs/0907.2954). Their Theorem 4.15 gives an
independent paper proof via preservation of non-strong-collapsibility.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Topology.StableCategory.ProductStableLower

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd includeVertex ambientAtDepth
  baseAtDepth_le baseVertexAtDepth retainedVertex subdividedVertex MaximalFaceCriterion
  contiguity_chain_fixes_original_vertices)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open ConnectedCategoryGraft (HasCategoricalCover)
open OrdinaryContiguityLift (comp_chains include_subcomplex_simplicial Simplicial)
open OrdinarySubdivisionTransfer (finiteSpaceSubdivision)
open ProductRigidCores (P Factor ProductPoset VertexLabel boundary corner)
open SubdivisionCategoricalCover (subdivision_map_fence)
open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open Relation (EqvGen ReflTransGen)

open private singletonFace from D5.S3.Topology.BarycentricGraphDistance
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private mem_generated boundaryEdges boundary_le boundary_edge_index boundary_edge_mem
  from D5.S3.Topology.StableCategory.ProductRigidCores
open private chainsCongr subdivisionFace from
  D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
open private map_fence orderHomMap_const singletonChain from
  D5.S3.Topology.SubdivisionCategoricalCover

section FaceFences

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {V : Type} {K : PreAbstractSimplicialComplex V}

private def chooseVertex (s : Face K) : Vertex K := by
  let h := (K.isRelLowerSet_faces s.property).1
  exact ⟨h.choose, (K.isRelLowerSet_faces s.property).2
    (Finset.singleton_subset_iff.mpr h.choose_spec) (Finset.singleton_nonempty _)⟩

private theorem chooseVertex_mem (s : Face K) : (chooseVertex s).val ∈ s.val :=
  (K.isRelLowerSet_faces s.property).1.choose_spec

private def chooseOnSingletons (f : Face K →o Face K) (v : Vertex K) : Vertex K :=
  chooseVertex (f (singletonFace v))

private theorem contiguous_of_faceMap_le {f g : Face K →o Face K} (hfg : f ≤ g) :
    Contiguous (chooseOnSingletons f) (chooseOnSingletons g) := by
  intro s hs
  let t : Face K := ⟨s, hs⟩
  have image_subset (h : Face K →o Face K) (hh : h ≤ g) :
      faceImage (chooseOnSingletons h) hs ⊆ (g t).val := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff (chooseOnSingletons h) hs y).mp hy
    have hvt : singletonFace v ≤ t := Finset.singleton_subset_iff.mpr hv
    exact (g.monotone hvt) ((OrderHom.le_def.mp hh (singletonFace v)) (chooseVertex_mem _))
  exact (K.isRelLowerSet_faces (g t).property).2
    (Finset.union_subset (image_subset f hfg) (image_subset g le_rfl))
    (((K.isRelLowerSet_faces hs).1.attach.image _).mono Finset.subset_union_left)

/-- A contraction fence on nonempty faces induces a contiguity chain at the
depth of the complex whose faces occur in the fence. -/
theorem id_contiguity_of_face_poset_contraction (c : Face K)
    (h : EqvGen (· ≤ ·) (OrderHom.id : Face K →o Face K) (OrderHom.const _ c)) :
    ∃ b : Vertex K, ReflTransGen Contiguous (id : Vertex K → Vertex K) (fun _ => b) := by
  have reverse {f g : Vertex K → Vertex K} (hfg : ReflTransGen Contiguous f g) :
      ReflTransGen Contiguous g f := by
    induction hfg with
    | refl => exact .refl
    | tail _ hstep ih =>
      exact (ReflTransGen.single (fun s hs => by
        rw [Finset.union_comm]
        exact hstep s hs)).trans ih
  have lift {f g : Face K →o Face K} (hfg : EqvGen (· ≤ ·) f g) :
      ReflTransGen Contiguous (chooseOnSingletons f) (chooseOnSingletons g) := by
    induction hfg with
    | rel _ _ hle => exact .single (contiguous_of_faceMap_le hle)
    | refl => exact .refl
    | symm _ _ _ ih => exact reverse ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hstart : chooseOnSingletons (OrderHom.id : Face K →o Face K) = id := by
    funext v
    exact Subtype.ext (Finset.mem_singleton.mp (chooseVertex_mem (singletonFace v)))
  have hfinish : chooseOnSingletons (OrderHom.const (Face K) c) = fun _ => chooseVertex c :=
    rfl
  exact ⟨chooseVertex c, by simpa only [hstart, hfinish] using lift h⟩

end FaceFences

private theorem boundary_edge_max_table :
    ∀ e ∈ boundaryEdges, ∀ t ∈ boundaryEdges, e ⊆ t → t ⊆ e := by
  decide +kernel

private theorem boundary_edge_max (e : Finset VertexLabel) (he : e ∈ boundaryEdges) :
    ∃ F : Face boundary, F.val = e ∧ IsMax F := by
  obtain ⟨i, rfl⟩ := boundary_edge_index e he
  let F : Face boundary := ⟨_, boundary_edge_mem i⟩
  refine ⟨F, rfl, ?_⟩
  intro U hFU
  obtain ⟨_, t, ht, hUt⟩ := mem_generated.mp U.property
  have heU : F.val ⊆ U.val := hFU
  exact hUt.trans (boundary_edge_max_table _ he t ht (heU.trans hUt))

private theorem boundary_criterion_table :
    ∀ a w : VertexLabel, ({a} : Finset VertexLabel) ∈ boundary →
      (∀ e ∈ boundaryEdges, a ∈ e → insert w e ∈ P) → w = a := by
  simp only [mem_generated]
  decide +kernel

private theorem boundary_criterion : MaximalFaceCriterion P boundary := by
  intro a w h
  apply boundary_criterion_table a.val w a.property
  intro e he ha
  obtain ⟨F, rfl, hF⟩ := boundary_edge_max e he
  have eq : @insert VertexLabel (Finset VertexLabel)
      (@Finset.instInsert VertexLabel (Classical.decEq VertexLabel)) w F.val =
      insert w F.val := by
    ext x
    simp only [Finset.mem_insert]
  rw [← eq]
  exact h F hF ha

private theorem retained_vertex_injective {V : Type} {K : PreAbstractSimplicialComplex V}
    (n : ℕ) : Function.Injective (retainedVertex (J := K) n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    intro a b h
    apply ih
    apply Subtype.ext
    apply Finset.singleton_injective
    exact congrArg (fun v : Vertex (iteratedAmbient K (n + 1)).2 => v.val.val) h

private def boundaryOne : Vertex boundary := ⟨1, by rw [mem_generated]; decide +kernel⟩
private def boundaryTwo : Vertex boundary := ⟨2, by rw [mem_generated]; decide +kernel⟩

/-- The identity at every positive ordinary depth of the factor has no
contiguity chain to a constant, by restriction to the same-depth boundary. -/
theorem subdivision_not_contiguous_to_constant (r : ℕ)
    (b : Vertex (ambientAtDepth P (r + 1)).2) :
    ¬ ReflTransGen Contiguous (id : Vertex (ambientAtDepth P (r + 1)).2 → _)
      (fun _ => b) := by
  intro h
  let inc := includeVertex (baseAtDepth_le boundary_le (r + 1))
  have hinc : Simplicial inc :=
    include_subcomplex_simplicial (baseAtDepth_le boundary_le (r + 1))
  have hid : Simplicial (id : Vertex (ambientAtDepth P (r + 1)).2 → _) :=
    include_subcomplex_simplicial (le_refl _)
  have hboundary : ReflTransGen Contiguous inc (fun _ => b) :=
    comp_chains inc id hinc hid h
  have h₁ := contiguity_chain_fixes_original_vertices boundary_le boundary_criterion
    (r + 1) hboundary boundaryOne
  have h₂ := contiguity_chain_fixes_original_vertices boundary_le boundary_criterion
    (r + 1) hboundary boundaryTwo
  have he : retainedVertex r (subdividedVertex (includeVertex boundary_le boundaryOne)) =
      retainedVertex r (subdividedVertex (includeVertex boundary_le boundaryTwo)) :=
    h₁.symm.trans h₂
  have hsingle := congrArg (fun v : Vertex (sd P) => v.val.val)
    (retained_vertex_injective r he)
  change ({1} : Finset VertexLabel) = {2} at hsingle
  exact (by decide +kernel : ({1} : Finset VertexLabel) ≠ {2}) hsingle

section OrderFences

variable {X Y : Type} [PartialOrder X] [PartialOrder Y]

private def Contracts (X : Type) [PartialOrder X] : Prop :=
  ∃ c : X, EqvGen (· ≤ ·) (OrderHom.id : X →o X) (OrderHom.const X c)

private theorem contracts_of_small_cover (p : X) {k : ℕ} (hk : k < 2)
    (h : HasCategoricalCover X k) : Contracts X := by
  obtain ⟨U, hU, cover⟩ := h
  obtain ⟨i, _⟩ := cover p
  have all (x : X) : x ∈ U i := by
    obtain ⟨j, hj⟩ := cover x
    have hji : j = i := by
      apply Fin.ext
      have hk' : k ≤ 1 := Nat.le_of_lt_succ hk
      have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (i.isLt.trans_le hk'))
      have hj : j.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (j.isLt.trans_le hk'))
      exact hj.trans hi.symm
    exact hji ▸ hj
  obtain ⟨c, hc⟩ := (hU i).2
  let pre : X →o U i := ⟨fun x => ⟨x, all x⟩, fun _ _ hxy => hxy⟩
  let lift (f : U i →o X) : X →o X := f.comp pre
  have hf := map_fence lift
    (fun _ _ hfg => .rel _ _ (fun x => OrderHom.le_def.mp hfg (pre x))) hc
  have start : lift (OrderEmbedding.subtype (U i)).toOrderHom = OrderHom.id := rfl
  have finish : lift (OrderHom.const (U i) c) = OrderHom.const X c := rfl
  exact ⟨c, by simpa only [start, finish] using hf⟩

private theorem contracts_retract (embed : X →o Y) (project : Y →o X)
    (hleft : Function.LeftInverse project embed) (h : Contracts Y) : Contracts X := by
  obtain ⟨c, hc⟩ := h
  let lift (f : Y →o Y) : X →o X := project.comp (f.comp embed)
  have hf := map_fence lift (fun _ _ hfg => .rel _ _
    (fun x => project.monotone (OrderHom.le_def.mp hfg (embed x)))) hc
  have start : lift OrderHom.id = OrderHom.id := by
    apply OrderHom.ext
    exact funext hleft
  have finish : lift (OrderHom.const Y c) = OrderHom.const X (project c) := rfl
  exact ⟨project c, by simpa only [start, finish] using hf⟩

private def depthMap (f : X →o Y) (r : ℕ) :
    letI : PartialOrder (finiteSpaceSubdivision X r).1 := (finiteSpaceSubdivision X r).2
    letI : PartialOrder (finiteSpaceSubdivision Y r).1 := (finiteSpaceSubdivision Y r).2
    (finiteSpaceSubdivision X r).1 →o (finiteSpaceSubdivision Y r).1 := by
  induction r with
  | zero => exact f
  | succ r ih =>
    letI : PartialOrder (finiteSpaceSubdivision X r).1 := (finiteSpaceSubdivision X r).2
    letI : PartialOrder (finiteSpaceSubdivision Y r).1 := (finiteSpaceSubdivision Y r).2
    exact orderHomMap ih

private theorem depthMap_leftInverse (embed : X →o Y) (project : Y →o X)
    (hleft : Function.LeftInverse project embed) (r : ℕ) :
    Function.LeftInverse (depthMap project r) (depthMap embed r) := by
  classical
  induction r with
  | zero => exact hleft
  | succ r ih =>
    letI : PartialOrder (finiteSpaceSubdivision X r).1 := (finiteSpaceSubdivision X r).2
    letI : PartialOrder (finiteSpaceSubdivision Y r).1 := (finiteSpaceSubdivision Y r).2
    intro s
    apply NonemptyFiniteChains.ext
    change (s.finset.image (depthMap embed r)).image (depthMap project r) = s.finset
    rw [Finset.image_image]
    calc
      s.finset.image (depthMap project r ∘ depthMap embed r) =
          s.finset.image id := Finset.image_congr (fun x _ => ih x)
      _ = s.finset := Finset.image_id

private theorem depth_finite (X : Type) [PartialOrder X] [Finite X] (r : ℕ) :
    Finite (finiteSpaceSubdivision X r).1 := by
  induction r with
  | zero => exact inferInstanceAs (Finite X)
  | succ r ih =>
    letI : PartialOrder (finiteSpaceSubdivision X r).1 := (finiteSpaceSubdivision X r).2
    letI : Finite (finiteSpaceSubdivision X r).1 := ih
    letI := Fintype.ofFinite (finiteSpaceSubdivision X r).1
    exact Finite.of_injective
      (fun s : NonemptyFiniteChains (finiteSpaceSubdivision X r).1 => s.finset)
      (fun _ _ h => NonemptyFiniteChains.ext h)

private theorem contracts_chains [Finite X] (h : Contracts X) :
    Contracts (NonemptyFiniteChains X) := by
  classical
  obtain ⟨c, hc⟩ := h
  have hstart : orderHomMap (OrderHom.id : X →o X) = OrderHom.id := by
    apply OrderHom.ext
    funext s
    apply NonemptyFiniteChains.ext
    exact Finset.image_id
  have hf := subdivision_map_fence hc
  rw [hstart, orderHomMap_const] at hf
  exact ⟨singletonChain c, hf⟩

end OrderFences

private def factorFaces (r : ℕ) :
    letI : PartialOrder (finiteSpaceSubdivision Factor r).1 :=
      (finiteSpaceSubdivision Factor r).2
    Face (ambientAtDepth P r).2 ≃o (finiteSpaceSubdivision Factor r).1 := by
  cases r with
  | zero => exact OrderIso.refl _
  | succ r =>
    induction r with
    | zero => exact subdivisionFace P
    | succ r ih =>
      letI : PartialOrder (finiteSpaceSubdivision Factor (r + 1)).1 :=
        (finiteSpaceSubdivision Factor (r + 1)).2
      change Face (sd (ambientAtDepth P (r + 1)).2) ≃o
        NonemptyFiniteChains (finiteSpaceSubdivision Factor (r + 1)).1
      exact OrderIso.trans (subdivisionFace (ambientAtDepth P (r + 1)).2) (chainsCongr ih)

private def productSection : Factor →o ProductPoset :=
  ⟨fun a => (a, corner 0), fun _ _ h => ⟨h, le_rfl⟩⟩

/-- Every categorical lower cover of the ordinary depth-`r` product has at
least two pieces. Each inclusion contracts in that same depth-`r` ambient poset. -/
theorem product_cover_lower_at_depth (r k : ℕ)
    (cover : @HasCategoricalCover (finiteSpaceSubdivision ProductPoset r).1
      (finiteSpaceSubdivision ProductPoset r).2 k) : 2 ≤ k := by
  by_contra h
  letI : PartialOrder (finiteSpaceSubdivision Factor r).1 :=
    (finiteSpaceSubdivision Factor r).2
  letI : PartialOrder (finiteSpaceSubdivision ProductPoset r).1 :=
    (finiteSpaceSubdivision ProductPoset r).2
  let embed := depthMap productSection r
  let project := depthMap (OrderHom.fst : ProductPoset →o Factor) r
  have hleft : Function.LeftInverse project embed :=
    depthMap_leftInverse productSection OrderHom.fst (fun _ => rfl) r
  let point := (factorFaces r) (singletonFace
    (includeVertex (baseAtDepth_le boundary_le r)
      (baseVertexAtDepth boundary_le r boundaryOne)))
  have hprod := contracts_of_small_cover (embed point) (Nat.lt_of_not_ge h) cover
  have hfactor := contracts_retract embed project hleft hprod
  letI : Finite Factor := Finite.of_injective (fun a : Factor => a.val) Subtype.val_injective
  letI : Finite (finiteSpaceSubdivision Factor r).1 := depth_finite Factor r
  have hchains := contracts_chains hfactor
  letI : PartialOrder (finiteSpaceSubdivision Factor (r + 1)).1 :=
    (finiteSpaceSubdivision Factor (r + 1)).2
  let e := factorFaces (r + 1)
  have hnext : Contracts (finiteSpaceSubdivision Factor (r + 1)).1 := hchains
  obtain ⟨c, hc⟩ := contracts_retract
    (⟨e, e.monotone⟩ : Face (ambientAtDepth P (r + 1)).2 →o
      (finiteSpaceSubdivision Factor (r + 1)).1)
    ⟨e.symm, e.symm.monotone⟩ e.symm_apply_apply hnext
  obtain ⟨b, hb⟩ := id_contiguity_of_face_poset_contraction c hc
  exact subdivision_not_contiguous_to_constant r b hb

/-- The least categorical lower cover size over all common ordinary subdivision depths is two. -/
theorem product_stable_category_eq_two :
    IsLeast {k : ℕ | ∃ r : ℕ, @HasCategoricalCover
      (finiteSpaceSubdivision ProductPoset r).1 (finiteSpaceSubdivision ProductPoset r).2 k} 2 := by
  refine ⟨⟨2, ProductStableCover.product_two_after_two_subdivisions⟩, ?_⟩
  rintro k ⟨r, cover⟩
  exact product_cover_lower_at_depth r k cover

end D5.S3.Topology.StableCategory.ProductStableLower
