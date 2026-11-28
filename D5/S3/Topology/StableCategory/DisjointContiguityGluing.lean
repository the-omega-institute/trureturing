/- GID: D5/S3/Topology/StableCategory/DisjointContiguityGluing
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contiguity chains coexist across disjoint induced components. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.OrdinaryCollarRetraction
import D5.S3.Topology.StableCategory.OrdinaryContiguityLift

/-! Contiguity factorizations on a facewise disjoint partition. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.DisjointContiguityGluing

open BarycentricGraphDistance (Vertex)
open BarycentricBaseRigidity (Contiguous faceImage)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial)
open Relation (ReflTransGen)
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

private theorem finite_product_chain {ι : Type} [Fintype ι]
    {U : ι → Type} (r : ∀ i, U i → U i → Prop)
    (reflexive : ∀ i x, r i x x) (f g : ∀ i, U i)
    (h : ∀ i, ReflTransGen (r i) (f i) (g i)) :
    ReflTransGen (fun a b => ∀ i, r i (a i) (b i)) f g := by
  let R (a b : ∀ i, U i) : Prop := ∀ i, r i (a i) (b i)
  let mixed (s : Finset ι) (i : ι) : U i := if i ∈ s then g i else f i
  have reach (s : Finset ι) : ReflTransGen R f (mixed s) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : mixed ∅ = f := by funext i; simp [mixed]
      rw [he]
    | @insert i s hi ih =>
      let changeAt (x : U i) := Function.update (mixed s) i x
      have start : changeAt (f i) = mixed s := by
        apply Function.update_eq_self_iff.mpr
        simp [mixed, hi]
      have finish : changeAt (g i) = mixed (insert i s) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [changeAt, mixed]
        · simp [changeAt, Function.update_of_ne hj, mixed, Finset.mem_insert, hj]
      have step (a b : U i) (hab : r i a b) : R (changeAt a) (changeAt b) := by
        intro j
        by_cases hj : j = i
        · subst j
          simpa [changeAt] using hab
        · simpa only [changeAt, Function.update_of_ne hj] using reflexive j (mixed s j)
      have hchange : ReflTransGen R (changeAt (f i)) (changeAt (g i)) :=
        ReflTransGen.lift changeAt (fun _ _ hab => step _ _ hab) _ _ (h i)
      rw [start, finish] at hchange
      exact ih.trans hchange
  have he : mixed Finset.univ = g := by funext i; simp [mixed]
  exact he ▸ reach Finset.univ

variable {X Y ι : Type} {P : PreAbstractSimplicialComplex X}
  {Q : PreAbstractSimplicialComplex Y}

private def colourPiece (label : X → ι) (i : ι) :=
  colourComplex P (fun x => decide (label x = i))

private def labelledVertex (label : X → ι) (x : Vertex P) :
    Vertex (colourPiece (P := P) label (label x.val)) :=
  ⟨x.val, x.property, by
    intro y hy
    rw [Finset.mem_singleton.mp hy]
    exact decide_eq_true rfl⟩

private def glue (label : X → ι)
    (f : ∀ i, Vertex (colourPiece (P := P) label i) → Vertex Q) : Vertex P → Vertex Q :=
  fun x => f (label x.val) (labelledVertex label x)

private theorem faceImage_glue (label : X → ι)
    (f : ∀ i, Vertex (colourPiece (P := P) label i) → Vertex Q)
    {s : Finset X} (hs : s ∈ P) (i : ι) (hi : ∀ x ∈ s, label x = i) :
    faceImage (glue label f) hs =
      faceImage (f i) (show s ∈ colourPiece label i from
        ⟨hs, fun x hx => decide_eq_true (hi x hx)⟩) := by
  unfold faceImage
  apply Finset.image_congr
  intro x _
  simp only [glue]
  have he : label x.val = i := hi _ x.property
  subst i
  rfl

/-- A vertex map built separately on the parts of a facewise disjoint
partition is simplicial whenever each of its restrictions is. -/
theorem glue_simplicial (label : X → ι)
    (hface : ∀ s ∈ P, ∃ i, ∀ x ∈ s, label x = i)
    (f : ∀ i, Vertex (colourPiece (P := P) label i) → Vertex Q)
    (hf : ∀ i, Simplicial (f i)) : Simplicial (glue label f) := by
  intro s hs
  obtain ⟨i, hi⟩ := hface s hs
  rw [faceImage_glue label f hs i hi]
  exact hf i _ _

/-- On a finite union in which each face belongs to a single part, contiguity
chains on the parts can be applied together in the same target. -/
theorem glue_contiguity [Fintype ι] (label : X → ι)
    (hface : ∀ s ∈ P, ∃ i, ∀ x ∈ s, label x = i)
    (f g : ∀ i, Vertex (colourPiece (P := P) label i) → Vertex Q)
    (hf : ∀ i, Contiguous (f i) (f i)) (hg : ∀ i, Contiguous (g i) (g i))
    (h : ∀ i, ReflTransGen Contiguous (f i) (g i)) :
    ReflTransGen Contiguous (glue label f) (glue label g) := by
  let U i := {a : Vertex (colourPiece (P := P) label i) → Vertex Q // Contiguous a a}
  let r (i : ι) (a b : U i) := Contiguous a.val b.val
  let G (a : ∀ i, U i) := glue label (fun i => (a i).val)
  let F₀ (i : ι) : U i := ⟨f i, hf i⟩
  let F₁ (i : ι) : U i := ⟨g i, hg i⟩
  have hpart (i : ι) : ReflTransGen (r i) (F₀ i) (F₁ i) := by
    have lift {b : Vertex (colourPiece (P := P) label i) → Vertex Q}
        (hb : ReflTransGen Contiguous (f i) b) :
        ∀ hbb : Contiguous b b, ReflTransGen (r i) (F₀ i) ⟨b, hbb⟩ := by
      induction hb with
      | refl => exact fun _ => .refl
      | @tail a b _ hab ih =>
        intro hbb
        have haa : Contiguous a a := by
          intro s hs
          rw [Finset.union_idempotent]
          exact (Q.isRelLowerSet_faces (hab s hs)).2 Finset.subset_union_left
            (((colourPiece (P := P) label i).isRelLowerSet_faces hs).1.attach.image _)
        exact (ih haa).tail (show r i ⟨a, haa⟩ ⟨b, hbb⟩ from hab)
    exact lift (h i) (hg i)
  have compatible (a b : ∀ i, U i) (hab : ∀ i, r i (a i) (b i)) :
      Contiguous (G a) (G b) := by
    intro s hs
    obtain ⟨i, hi⟩ := hface s hs
    have hs' : s ∈ colourPiece (P := P) label i :=
      ⟨hs, fun x hx => decide_eq_true (hi x hx)⟩
    have image_eq (u : ∀ i, U i) : faceImage (G u) hs = faceImage (u i).val hs' := by
      exact faceImage_glue label (fun j => (u j).val) hs i hi
    rw [image_eq a, image_eq b]
    exact hab i s hs'
  exact ReflTransGen.lift G compatible _ _
    (finite_product_chain r (fun _ a => a.property) F₀ F₁ hpart)

section Parameters

variable {V : ι → Type} (G : ∀ j, PreAbstractSimplicialComplex (V j))

/-- The disjoint union of the parameter complexes of the pieces. -/
def parameterUnion : PreAbstractSimplicialComplex (Σ j, V j) :=
  ⨆ j, (G j).map (Sigma.mk j)

private theorem mem_parameterUnion (s : Finset (Σ j, V j)) :
    s ∈ parameterUnion G ↔ ∃ j t, t ∈ G j ∧ t.image (Sigma.mk j) = s := by
  change (s ∈ ⋃ K ∈ Set.range (fun j => (G j).map (Sigma.mk j)), K.faces) ↔ _
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨K, ⟨j, rfl⟩, ⟨t, ht, h⟩⟩
    exact ⟨j, t, ht, h⟩
  · rintro ⟨j, t, ht, h⟩
    exact ⟨_, ⟨j, rfl⟩, ⟨t, ht, h⟩⟩

theorem parameter_union_card {n : ℕ} (bound : ∀ j s, s ∈ G j → s.card ≤ n) :
    ∀ s ∈ parameterUnion G, s.card ≤ n := by
  intro s hs
  obtain ⟨j, t, ht, rfl⟩ := (mem_parameterUnion G s).1 hs
  exact Finset.card_image_le.trans (bound j t ht)

theorem parameter_union_rank {n : ℕ} (rank : ∀ j, V j → Fin n)
    (proper : ∀ j s, s ∈ G j → Set.InjOn (rank j) (s : Set (V j))) :
    ∀ s ∈ parameterUnion G, Set.InjOn (fun x => rank x.1 x.2) (s : Set (Σ j, V j)) := by
  intro s hs u hu v hv he
  obtain ⟨j, t, ht, rfl⟩ := (mem_parameterUnion G s).1 hs
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  exact congrArg (Sigma.mk j) (proper j t ht hx hy he)

private def toUnion (j : ι) (v : Vertex (G j)) : Vertex (parameterUnion G) :=
  ⟨⟨j, v.val⟩, (mem_parameterUnion G _).2
    ⟨j, {v.val}, v.property, Finset.image_singleton _ _⟩⟩

private def fromUnion (v : Vertex (parameterUnion G)) : Vertex (G v.val.1) :=
  ⟨v.val.2, by
    obtain ⟨j, t, ht, h⟩ := (mem_parameterUnion G _).1 v.property
    have hv : v.val ∈ t.image (Sigma.mk j) := h.symm ▸ Finset.mem_singleton_self _
    obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hv
    rcases v with ⟨v, hv⟩
    change (⟨j, x⟩ : Σ j, V j) = v at hxv
    subst v
    exact ((G j).isRelLowerSet_faces ht).2
      (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)⟩

private theorem to_union_simplicial (j : ι) : Simplicial (toUnion G j) := by
  intro s hs
  apply (mem_parameterUnion G _).2
  refine ⟨j, s, hs, ?_⟩
  ext y
  simp only [Finset.mem_image, mem_faceImage_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := ((G j).isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty _)
    exact ⟨⟨x, hx'⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩

/-- Map each component of a disjoint union using its own simplicial map. -/
def parameterMap (g : ∀ j, Vertex (G j) → Vertex Q) :
    Vertex (parameterUnion G) → Vertex Q :=
  fun v => g v.val.1 (fromUnion G v)

theorem parameter_map_simplicial (g : ∀ j, Vertex (G j) → Vertex Q)
    (hg : ∀ j, Simplicial (g j)) : Simplicial (parameterMap G g) := by
  intro s hs
  obtain ⟨j, t, ht, h⟩ := (mem_parameterUnion G s).1 hs
  have he : faceImage (parameterMap G g) hs = faceImage (g j) ht := by
    ext y
    simp only [mem_faceImage_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [← h] at hv
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hv
      have hx' : ({x} : Finset _) ∈ G j :=
        ((G j).isRelLowerSet_faces ht).2 (Finset.singleton_subset_iff.mpr hx)
          (Finset.singleton_nonempty _)
      let z : Vertex (G j) := ⟨x, hx'⟩
      have hv' : toUnion G j z = v := Subtype.ext he
      exact ⟨z, hx, congrArg (fun a => (parameterMap G g a).val) hv'⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨toUnion G j v, h ▸ Finset.mem_image.mpr ⟨v.val, hv, rfl⟩, rfl⟩
  rw [he]
  exact hg j _ ht

/-- Contiguity factorizations on facewise disjoint parts combine into a
factorization through the disjoint union of their parameter complexes. -/
theorem glue_factorizations [Fintype ι] (label : X → ι)
    (hface : ∀ s ∈ P, ∃ j, ∀ x ∈ s, label x = j)
    (f : Vertex P → Vertex Q) (hf : Simplicial f)
    (h : ∀ j, Vertex (colourPiece (P := P) label j) → Vertex (G j))
    (g : ∀ j, Vertex (G j) → Vertex Q)
    (hh : ∀ j, Simplicial (h j)) (hg : ∀ j, Simplicial (g j))
    (chains : ∀ j, ReflTransGen Contiguous
      (fun v : Vertex (colourPiece (P := P) label j) => f ⟨v.val, v.property.1⟩)
      (g j ∘ h j)) :
    ∃ a : Vertex P → Vertex (parameterUnion G), Simplicial a ∧
      ReflTransGen Contiguous f (parameterMap G g ∘ a) := by
  let a := glue label (fun j => toUnion G j ∘ h j)
  have ha := glue_simplicial label hface (fun j => toUnion G j ∘ h j)
    (fun j => (to_union_simplicial G j).comp (hh j))
  have self_comp {S : PreAbstractSimplicialComplex X}
      {v : Vertex S → Vertex Q} (hv : Simplicial v) : Contiguous v v := by
    intro s hs
    rw [Finset.union_idempotent]
    exact hv s hs
  let inc (j : ι) := OrdinaryContiguityLift.includeSubcomplex
    (show colourPiece (P := P) label j ≤ P from fun _ hs => hs.1)
  have hinc : ∀ j, Simplicial (inc j) := fun j =>
    OrdinaryContiguityLift.include_subcomplex_simplicial _
  have hchain := glue_contiguity label hface (fun j => f ∘ inc j) (fun j => g j ∘ h j)
    (fun j => self_comp (hf.comp (hinc j))) (fun j => self_comp ((hg j).comp (hh j))) chains
  exact ⟨a, ha, hchain⟩

end Parameters

end

end D5.S3.Topology.StableCategory.DisjointContiguityGluing
