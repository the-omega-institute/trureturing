/- GID: D5/S3/Topology/StableCategory/OrdinaryCollarNaturality
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both ordinary collar cuts commute with colour-preserving maps. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
import D5.S3.Topology.StableCategory.OrdinaryContiguityLift

/-! Pulling back a two-cut collar and its contiguity comparisons. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.OrdinaryCollarNaturality

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd vertexOfFace)
open OrdinaryCollarRetraction (colourComplex retract retract_image)
open OrdinaryCollarContiguity (collarComplex collar_inclusion_contiguous)
open OrdinaryContiguityLift (Simplicial comp_chains comp_image includeSubcomplex
  include_subcomplex_simplicial iterate_comp lift_iterates ofTotal of_total_simplicial)
open OrdinarySubdivisionMap (iterate inTwoCutCollar inTwoCutCollar_iterate_iff twoCutImage_iterate)
open Relation (ReflTransGen)
open private collarVertex colour_inclusion_image forgetColour
  from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private image from D5.S3.Topology.OrdinarySubdivisionMap

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {X Y : Type} {K : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}

private theorem restricted_image (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (p : X → Bool) (q : Y → Bool) (hcolour : ∀ x, q (f x) = p x) :
    ∀ s ∈ colourComplex K p, image s f ∈ colourComplex L q := by
  intro s hs
  refine ⟨hf s hs.1, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (hcolour x).trans (hs.2 x hx)

variable {M : PreAbstractSimplicialComplex X} {N : PreAbstractSimplicialComplex Y}

private def erasedFlag (v : Face (sd (sd M))) : Finset (Finset (Finset X)) :=
  v.val.image fun b => b.val.image Subtype.val

private theorem erasedFlag_injective : Function.Injective (erasedFlag (M := M)) := by
  have h : Function.Injective (fun b : Face (sd M) => b.val.image Subtype.val) :=
    (Finset.image_injective Subtype.val_injective).comp Subtype.val_injective
  exact (Finset.image_injective h).comp Subtype.val_injective

private theorem erase_iterate (f : X → Y) (hf : ∀ s ∈ M, image s f ∈ N)
    (v : Face (sd (sd M))) :
    erasedFlag ((iterate f hf 3).val v) =
      image (erasedFlag v) (fun b => image b (fun a => image a f)) := by
  let f₁ := (iterate f hf 1).val
  let f₂ := (iterate f hf 2).val
  change (v.val.image f₂).image (fun b => b.val.image Subtype.val) =
    (v.val.image fun b => b.val.image Subtype.val).image (fun b => image b (fun a => image a f))
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro b _
  change (b.val.image f₁).image Subtype.val =
    (b.val.image Subtype.val).image (fun a => image a f)
  rw [Finset.image_image, Finset.image_image]
  rfl

/-- For a colour-preserving simplicial map, the ordinary two-cut retraction
commutes with the actual subdivided map on the selected colour complexes. -/
theorem retract_natural (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (p : X → Bool) (q : Y → Bool) (hcolour : ∀ x, q (f x) = p x)
    (v : Face (sd (sd K))) (hv : inTwoCutCollar p v) :
    let map := (iterate f hf 3).val
    let selected := (iterate f (restricted_image f hf p q hcolour) 3).val
    retract q ⟨map v, (inTwoCutCollar_iterate_iff f hf p q hcolour v).2 hv⟩ =
      selected (retract p ⟨v, hv⟩) := by
  intro map selected
  apply erasedFlag_injective
  rw [erase_iterate]
  change erasedFlag (retract q ⟨map v, _⟩) =
    image (erasedFlag (retract p ⟨v, hv⟩)) (fun b => image b (fun a => image a f))
  simpa only [erasedFlag, retract_image] using twoCutImage_iterate f hf p q hcolour v

/-- The simplicial retraction of the two-cut collar onto the third
ordinary subdivision of its selected colour complex. -/
def retractMap (p : X → Bool) :
    Vertex (collarComplex K p) → Vertex (sd (sd (sd (colourComplex K p)))) :=
  fun v => vertexOfFace _ (retract p (collarVertex p v))

theorem retract_map_simplicial (p : X → Bool) : Simplicial (retractMap (K := K) p) := by
  intro s hs
  refine ⟨hs.1.1.attach.image _, ?_, fun a _ => a.property⟩
  intro a ha b hb hab
  obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff (retractMap p) hs a).mp ha
  obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff (retractMap p) hs b).mp hb
  have hne : u.val ≠ v.val := fun h => hab
    (congrArg (fun w : Vertex (collarComplex K p) => (retractMap p w).val) (Subtype.ext h))
  rcases hs.1.2.1 hu hv hne with h | h
  · exact Or.inl (lt_of_le_of_ne ((retract p).monotone h.le) hab)
  · exact Or.inr (lt_of_le_of_ne ((retract p).monotone h.le) hab.symm)

/-- If the selected part of a source map factors up to contiguity, the
map on its ordinary collar factors through the target collar retraction.
The homotopy takes place in the third subdivision of the ambient target. -/
theorem pullback_collar_chain [Finite X] {Z : Type}
    {A : PreAbstractSimplicialComplex Z}
    (i : X → Z) (hi : ∀ s ∈ K, image s i ∈ A)
    (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (p : X → Bool) (q : Y → Bool) (hcolour : ∀ x, q (f x) = p x)
    (g : Y → Z) (hg : ∀ s ∈ colourComplex L q, image s g ∈ A)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex K p) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ f) (comp_image f (restricted_image f hf p q hcolour) g hg))) :
    let B := sd (sd (sd A))
    let C := collarComplex K p
    let J := collarComplex L q
    ∃ pull : Vertex C → Vertex J, Simplicial pull ∧
      (∀ v, (pull v).val = (iterate f hf 3).val v.val) ∧
      ReflTransGen Contiguous
        (fun v : Vertex C =>
          ofTotal (iterate i hi 3).val (iterate i hi 3).property
            (includeSubcomplex (show C ≤ sd (sd (sd K)) from fun _ hs => hs.1) v))
        (fun v : Vertex C =>
          (ofTotal (K := sd (sd (sd (colourComplex L q)))) (L := B)
            (iterate g hg 3).val (iterate g hg 3).property) (retractMap q (pull v))) := by
  intro B C J
  let i₃ := iterate i hi 3
  let f₃ := iterate f hf 3
  let g₃ := iterate g hg 3
  let push := ofTotal i₃.val i₃.property
  let selected := restricted_image f hf p q hcolour
  have hiPart : ∀ s ∈ colourComplex K p, image s i ∈ A := fun s hs => hi s hs.1
  have hpart : ∀ s ∈ C, image s f₃.val ∈ J := by
    intro s hs
    refine ⟨f₃.property s hs.1, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact decide_eq_true ((inTwoCutCollar_iterate_iff f hf p q hcolour x).2
      (of_decide_eq_true (hs.2 x hx)))
  let pull := ofTotal f₃.val hpart
  refine ⟨pull, of_total_simplicial _ _, fun _ => rfl, ?_⟩
  let idC : Vertex C → Vertex C := id
  have hidC : Simplicial idC := include_subcomplex_simplicial (le_refl C)
  have hfirst := comp_chains idC push hidC (of_total_simplicial _ _)
    (collar_inclusion_contiguous (K := K) p)
  have hfibre := lift_iterates i (g ∘ f) hiPart (comp_image f selected g hg) old 3
  have hsecond := comp_chains (retractMap p) (id : Vertex B → Vertex B)
    (retract_map_simplicial p) (include_subcomplex_simplicial (le_refl B)) hfibre
  have hmiddle :
      (push ∘ (fun v : Vertex C => vertexOfFace (sd (sd K))
        ((forgetColour (K := K) p 3).val (retract p (collarVertex p v)))) ∘ idC) =
        id ∘ ofTotal (iterate i hiPart 3).val (iterate i hiPart 3).property ∘ retractMap p := by
    funext v
    apply Subtype.ext
    exact congrFun (iterate_comp id (colour_inclusion_image (K := K) p) i hi 3).symm
      (retract p (collarVertex p v))
  have hend : (id ∘
      ofTotal (iterate (g ∘ f) (comp_image f selected g hg) 3).val
        (iterate (g ∘ f) (comp_image f selected g hg) 3).property ∘ retractMap p) =
      (fun v => ofTotal g₃.val g₃.property (retractMap q (pull v))) := by
    funext v
    apply Subtype.ext
    change (iterate (g ∘ f) (comp_image f selected g hg) 3).val
        (retract p (collarVertex p v)) =
      g₃.val (retract q (collarVertex q (pull v)))
    rw [iterate_comp f selected g hg]
    exact congrArg g₃.val (retract_natural f hf p q hcolour v.val (collarVertex p v).property).symm
  rw [hmiddle] at hfirst
  rw [hend] at hsecond
  exact hfirst.trans hsecond

private theorem pullback_piece_chain [Finite X] {Z : Type} {A : PreAbstractSimplicialComplex Z}
    (i : X → Z) (hi : ∀ s ∈ K, image s i ∈ A)
    (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (p : X → Bool) (q : Y → Bool) (hcolour : ∀ x, q (f x) = p x)
    (g : Y → Z) (hg : ∀ s ∈ colourComplex L q, image s g ∈ A)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex K p) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ f) (comp_image f (restricted_image f hf p q hcolour) g hg)))
    {P : PreAbstractSimplicialComplex (Face (sd (sd K)))}
    {R : PreAbstractSimplicialComplex (Face (sd (sd L)))}
    (hp : P ≤ collarComplex K p) (hr : R ≤ collarComplex L q)
    (hm : ∀ s ∈ P, image s (iterate f hf 3).val ∈ R)
    (finish : Vertex R → Vertex (sd (sd (sd (colourComplex L q)))))
    (comparison : ReflTransGen Contiguous
      (retractMap q ∘ includeSubcomplex hr) finish) :
    ReflTransGen Contiguous
      (ofTotal (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s (hp hs).1))
      (ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ finish ∘
        ofTotal (iterate f hf 3).val hm) := by
  let B := sd (sd (sd A))
  let left := includeSubcomplex hp
  let pre := ofTotal (iterate f hf 3).val hm
  let post := ofTotal (iterate g hg 3).val (iterate g hg 3).property
  obtain ⟨pull, _, hpull, chain⟩ := pullback_collar_chain i hi f hf p q hcolour g hg old
  have hc := comp_chains left (id : Vertex B → Vertex B)
    (include_subcomplex_simplicial hp) (include_subcomplex_simplicial (le_refl B)) chain
  have endpoint : pull ∘ left = includeSubcomplex hr ∘ pre := by
    funext v
    apply Subtype.ext
    exact hpull (left v)
  have hstart :
      (id ∘ (fun v : Vertex (collarComplex K p) =>
        ofTotal (iterate i hi 3).val (iterate i hi 3).property
          (includeSubcomplex (show collarComplex K p ≤ sd (sd (sd K)) from fun _ hs => hs.1) v))
        ∘ left) =
        ofTotal (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s (hp hs).1) := rfl
  rw [hstart] at hc
  have hmiddle :
      (id ∘ (fun v : Vertex (collarComplex K p) => post (retractMap q (pull v))) ∘ left) =
        post ∘ (retractMap q ∘ includeSubcomplex hr) ∘ pre := by
    funext v
    exact congrArg (post ∘ retractMap q) (congrFun endpoint v)
  rw [hmiddle] at hc
  exact hc.trans (comp_chains pre post
    (of_total_simplicial _ _) (of_total_simplicial _ _) comparison)

/-- The faces of a source subdivision whose images are in a specified
target subcomplex. -/
def pullback {U V : Type} (P : PreAbstractSimplicialComplex U)
    (f : U → V) (R : PreAbstractSimplicialComplex V) : PreAbstractSimplicialComplex U where
  faces := {s | s ∈ P ∧ image s f ∈ R}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(P.isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts ht
    exact ⟨(P.isRelLowerSet_faces hs.1).2 hts ht,
      (R.isRelLowerSet_faces hs.2).2 (Finset.image_subset_image hts) (ht.image _)⟩

/-- A contiguity comparison on a target collar piece pulls back after
lifting the old colour factorization to the third subdivision. -/
theorem pullback_comparison [Finite X] {Z : Type} {A : PreAbstractSimplicialComplex Z}
    (i : X → Z) (hi : ∀ s ∈ K, image s i ∈ A)
    (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (q : Y → Bool) (g : Y → Z) (hg : ∀ s ∈ colourComplex L q, image s g ∈ A)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex K (q ∘ f)) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ f) (comp_image f (restricted_image f hf (q ∘ f) q (fun _ => rfl)) g hg)))
    {R : PreAbstractSimplicialComplex (Face (sd (sd L)))} (hr : R ≤ collarComplex L q)
    (finish : Vertex R → Vertex (sd (sd (sd (colourComplex L q)))))
    (comparison : ReflTransGen Contiguous
      (retractMap q ∘ includeSubcomplex hr) finish) :
    let P := pullback (sd (sd (sd K))) (iterate f hf 3).val R
    ReflTransGen Contiguous
      (ofTotal (K := P) (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1))
      (ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ finish ∘
        ofTotal (K := P) (iterate f hf 3).val (fun _ hs => hs.2)) := by
  intro P
  have hp : P ≤ collarComplex K (q ∘ f) := by
    intro s hs
    refine ⟨hs.1, fun u hu => decide_eq_true ?_⟩
    apply (inTwoCutCollar_iterate_iff f hf (q ∘ f) q (fun _ => rfl) u).1
    exact of_decide_eq_true ((hr hs.2).2 _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
  exact pullback_piece_chain i hi f hf (q ∘ f) q (fun _ => rfl) g hg old hp hr
    (fun _ hs => hs.2) finish comparison

end

end D5.S3.Topology.StableCategory.OrdinaryCollarNaturality
