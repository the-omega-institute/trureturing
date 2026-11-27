/- GID: D5/S3/Topology/StableCategory/OrdinaryCollarContiguity
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Two successive face cuts deform the ordinary collar inclusion in the fixed subdivision. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.OrdinaryCollarRetraction
import D5.S3.Topology.DescendingClosureContiguity

/-! A comparison of face order maps on a collar gives a contiguity chain
in the actual ordinary subdivision. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.OrdinaryCollarContiguity

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd vertexOfFace)
open OrdinaryCollarRetraction (colourComplex retract)
open OrdinarySubdivisionMap (cutFace cutFlag inTwoCutCollar iterate)
open DescendingClosureContiguity (exists_relative_contiguity_of_le)
open Relation (ReflTransGen)
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private cutFlag_nonempty first second chain_image
  from D5.S3.Topology.OrdinaryCollarRetraction
open private image from D5.S3.Topology.OrdinarySubdivisionMap

noncomputable section

local instance (priority := 2000) (V : Type*) : DecidableEq V := Classical.decEq V
attribute [local instance] Classical.propDecidable

variable {X Y : Type} {K : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}

private def vertexIn {p : Face K → Bool} (u : Vertex (colourComplex (sd K) p)) :
    {v : Face K // p v = true} :=
  ⟨u.val, u.property.2 _ (Finset.mem_singleton_self _)⟩

private def mapCollar (p : Face K → Bool) (f : {v : Face K // p v = true} →o Face L) :
    Vertex (colourComplex (sd K) p) → Vertex (sd L) :=
  fun u => vertexOfFace L (f (vertexIn u))

/-- Pointwise descending face maps give a finite contiguity chain on the
full ordinary subdivision complex spanned by the selected faces. -/
private theorem descending_collar_maps [Finite X] (p : Face K → Bool)
    (f g : {v : Face K // p v = true} →o Face L) (hle : ∀ u, g u ≤ f u) :
    ReflTransGen Contiguous (mapCollar p f) (mapCollar p g) := by
  let _ := Fintype.ofFinite X
  let rank (v : {v : Face K // p v = true}) := v.val.val.card
  have hrank : StrictMono rank := fun _ _ h => Finset.card_lt_card h
  have hbound (v : {v : Face K // p v = true}) : rank v ≤ Fintype.card X :=
    Finset.card_le_univ _
  obtain ⟨F, hzero, hlast, _, _, hstep⟩ :=
    exists_relative_contiguity_of_le rank hrank f g hle _ hbound
  have hcontig (k : ℕ) : Contiguous (mapCollar p (F k)) (mapCollar p (F (k + 1))) := by
    intro s hs
    let S : Set {v : Face K // p v = true} := {v | v.val ∈ s}
    have hS : IsChain (· ≤ ·) S := by
      intro a ha b hb hab
      exact (hs.1.2.1 ha hb (fun e => hab (Subtype.ext e))).imp LT.lt.le LT.lt.le
    let a := mapCollar p (F k)
    let b := mapCollar p (F (k + 1))
    let t := faceImage a hs ∪ faceImage b hs
    have ht (v : Face L) (hv : v ∈ t) : v ∈ F k '' S ∪ F (k + 1) '' S := by
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff a hs v).mp hv
        exact Or.inl ⟨vertexIn u, hu, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff b hs v).mp hv
        exact Or.inr ⟨vertexIn u, hu, rfl⟩
    have hne : (faceImage a hs).Nonempty := hs.1.1.attach.image _
    refine ⟨hne.mono Finset.subset_union_left, ?_, fun v _ => v.property⟩
    intro u hu v hv huv
    exact (hstep k S hS (ht _ hu) (ht _ hv) huv).imp
      (fun h => lt_of_le_of_ne h huv) (fun h => lt_of_le_of_ne h huv.symm)
  have hF (k : ℕ) : ReflTransGen Contiguous (mapCollar p (F 0)) (mapCollar p (F k)) := by
    induction k with
    | zero => exact .refl
    | succ k ih => exact ih.tail (hcontig k)
  simpa only [hzero, hlast] using hF (Fintype.card X + 1)

private def survivesSecond (colour : X → Bool) (b : Face (sd K)) : Bool :=
  decide ((cutFlag colour b).Nonempty)

private abbrev MeetsColour (colour : X → Bool) :=
  {a : Face K // (cutFace colour a).Nonempty}

private abbrev SurvivingFlag (colour : X → Bool) :=
  {b : Face (sd K) // survivesSecond (K := K) colour b = true}

private def liftFirst (colour : X → Bool) (f : MeetsColour (K := K) colour →o Face K) :
    SurvivingFlag (K := K) colour →o Face (sd K) where
  toFun b := by
    let t := b.val.val.subtype fun a => (cutFace colour a).Nonempty
    have hne : t.Nonempty := by
      obtain ⟨a, ha, hsurvives⟩ := (cutFlag_nonempty colour b.val).mp
        (of_decide_eq_true b.property)
      exact ⟨⟨a, hsurvives⟩, Finset.mem_subtype.mpr ha⟩
    exact ⟨t.image f, hne.image _, chain_image f _ b.val.property.2.1,
      fun a _ => a.property⟩
  monotone' := fun _ _ h => Finset.image_subset_image (Finset.subtype_mono h)

private def survivingInclusion (colour : X → Bool) :
    SurvivingFlag (K := K) colour →o Face (sd K) :=
  ⟨Subtype.val, fun _ _ h => h⟩

private def meetingInclusion (colour : X → Bool) :
    MeetsColour (K := K) colour →o Face K :=
  ⟨Subtype.val, fun _ _ h => h⟩

/-- At the second level an outer flag can discard inner faces missing
the colour. The deletion deforms the inclusion within the fixed
ambient subdivision, without changing any surviving inner face. -/
private theorem trim_second_contiguous [Finite (Face K)] (colour : X → Bool) :
    let p := survivesSecond (K := K) colour
    ReflTransGen Contiguous (mapCollar p (survivingInclusion colour))
      (mapCollar p (liftFirst colour (meetingInclusion colour))) := by
  intro p
  apply descending_collar_maps
  intro b a ha
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_subtype.mp ha'

private def cutInAmbient (colour : X → Bool) : MeetsColour (K := K) colour →o Face K where
  toFun a := ⟨(first colour a).val, (first colour a).property.1⟩
  monotone' := fun _ _ h => (first colour).monotone h

private theorem collar_chain_symm {X Y : Type} {K : PreAbstractSimplicialComplex X}
    {L : PreAbstractSimplicialComplex Y} {f g : Vertex K → Vertex L}
    (h : ReflTransGen Contiguous f g) : ReflTransGen Contiguous g f := by
  induction h with
  | refl => exact .refl
  | tail _ hfg ih =>
    exact (ReflTransGen.single (fun s hs => by
      rw [Finset.union_comm]
      exact hfg s hs)).trans ih

private theorem lift_first_contiguous [Finite X] [Finite (Face K)] (colour : X → Bool) :
    let p := survivesSecond (K := K) colour
    ReflTransGen Contiguous
      (mapCollar p (liftFirst colour (meetingInclusion colour)))
      (mapCollar p (liftFirst colour (cutInAmbient colour))) := by
  intro p
  let _ := Fintype.ofFinite X
  let rank (a : MeetsColour (K := K) colour) := a.val.val.card
  have hrank : StrictMono rank := fun _ _ h => Finset.card_lt_card h
  have hbound (a : MeetsColour (K := K) colour) : rank a ≤ Fintype.card X := Finset.card_le_univ _
  have hle (a : MeetsColour (K := K) colour) :
      cutInAmbient colour a ≤ meetingInclusion colour a :=
    Finset.filter_subset _ _
  obtain ⟨F, hzero, hlast, _, _, hstep⟩ :=
    exists_relative_contiguity_of_le rank hrank _ _ hle _ hbound
  let G (k : ℕ) := liftFirst (K := K) colour (F k)
  have adjacent (k : ℕ) :
      ReflTransGen Contiguous (mapCollar p (G k)) (mapCollar p (G (k + 1))) := by
    let top : SurvivingFlag (K := K) colour →o Face (sd K) := {
      toFun b := by
        let S : Set (MeetsColour (K := K) colour) := {a | a.val ∈ b.val.val}
        have hS : IsChain (· ≤ ·) S := by
          intro a ha a' ha' hne
          exact (b.val.property.2.1 ha ha' (fun h => hne (Subtype.ext h))).imp
            LT.lt.le LT.lt.le
        let t := (G k b).val ∪ (G (k + 1) b).val
        have ht (a : Face K) (ha : a ∈ t) : a ∈ F k '' S ∪ F (k + 1) '' S := by
          rcases Finset.mem_union.mp ha with ha | ha
          · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
            exact Or.inl ⟨a', Finset.mem_subtype.mp ha', rfl⟩
          · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
            exact Or.inr ⟨a', Finset.mem_subtype.mp ha', rfl⟩
        refine ⟨t, (G k b).property.1.mono Finset.subset_union_left, ?_, fun a _ => a.property⟩
        intro a ha a' ha' hne
        exact (hstep k S hS (ht _ ha) (ht _ ha') hne).imp
          (fun h => lt_of_le_of_ne h hne) (fun h => lt_of_le_of_ne h hne.symm)
      monotone' := fun _ _ h => Finset.union_subset_union ((G k).monotone h)
        ((G (k + 1)).monotone h) }
    exact (collar_chain_symm (descending_collar_maps p top (G k)
      (fun _ => Finset.subset_union_left))).trans
      (descending_collar_maps p top (G (k + 1)) (fun _ => Finset.subset_union_right))
  have reach (k : ℕ) : ReflTransGen Contiguous (mapCollar p (G 0)) (mapCollar p (G k)) := by
    induction k with
    | zero => exact .refl
    | succ k ih => exact ih.trans (adjacent k)
  simpa only [G, hzero, hlast] using reach (Fintype.card X + 1)

/-- The collar in the ordinary third subdivision consists of flags
all of whose second-level vertices meet a first-level selected face. -/
def collarComplex (K : PreAbstractSimplicialComplex X) (colour : X → Bool) :
    PreAbstractSimplicialComplex (Face (sd (sd K))) :=
  colourComplex (sd (sd (sd K))) (fun v => decide (inTwoCutCollar colour v))

private def collarVertex (colour : X → Bool) (v : Vertex (collarComplex K colour)) :
    {v : Face (sd (sd K)) // inTwoCutCollar colour v} :=
  ⟨v.val, of_decide_eq_true (v.property.2 _ (Finset.mem_singleton_self _))⟩

private theorem colour_inclusion_image (colour : X → Bool) :
    ∀ s ∈ colourComplex K colour, image s id ∈ K := by
  intro s hs
  simpa only [Finset.image_id] using hs.1

private abbrev forgetColour (colour : X → Bool) (n : ℕ) :=
  iterate (K := colourComplex K colour) (L := K) id (colour_inclusion_image colour) n

private theorem liftFirst_cut_eq (colour : X → Bool) (b : SurvivingFlag (K := K) colour) :
    liftFirst (K := K) colour (cutInAmbient (K := K) colour) b =
      (forgetColour (K := K) colour 2).val
        (second colour ⟨b.val, of_decide_eq_true b.property⟩) := by
  apply Subtype.ext
  change (b.val.val.subtype _).image (cutInAmbient (K := K) colour) =
    ((b.val.val.subtype _).image (first colour)).image (forgetColour (K := K) colour 1).val
  rw [Finset.image_image]
  apply Finset.image_congr
  intro a _
  apply Subtype.ext
  change (first colour a).val = ((first colour a).val).image id
  rw [Finset.image_id]

private def collarFace (colour : X → Bool) :
    {v : Face (sd (sd K)) // decide (inTwoCutCollar colour v) = true} →o
      Face (colourComplex (sd (sd K)) (survivesSecond (K := K) colour)) where
  toFun v := ⟨v.val.val, v.val.property, fun b hb =>
    decide_eq_true ((of_decide_eq_true v.property : inTwoCutCollar colour v.val) b hb)⟩
  monotone' := fun _ _ h => h

private theorem faceImage_mono {X Y : Type} {P : PreAbstractSimplicialComplex X}
    {Q : PreAbstractSimplicialComplex Y} (f : Vertex P → Vertex Q)
    {s t : Finset X} (hs : s ∈ P) (ht : t ∈ P) (h : s ⊆ t) :
    faceImage f hs ⊆ faceImage f ht := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff f hs y).mp hy
  exact (mem_faceImage_iff f ht _).mpr ⟨x, h hx, rfl⟩

private abbrev SecondVertexMap (colour : X → Bool) :=
  Vertex (colourComplex (sd (sd K)) (survivesSecond (K := K) colour)) → Vertex (sd (sd K))

private abbrev SimplicialSecondMap (colour : X → Bool) :=
  {f : SecondVertexMap (K := K) colour // Contiguous f f}

private theorem faceImage_mem {X Y : Type} {P : PreAbstractSimplicialComplex X}
    {Q : PreAbstractSimplicialComplex Y} {f : Vertex P → Vertex Q}
    (hf : Contiguous f f) {s : Finset X} (hs : s ∈ P) : faceImage f hs ∈ Q := by
  simpa only [Finset.union_idempotent] using hf s hs

private def liftSecondOrder (colour : X → Bool) (f : SimplicialSecondMap (K := K) colour) :
    {v : Face (sd (sd K)) // decide (inTwoCutCollar colour v) = true} →o Face (sd (sd K))
    where
  toFun v := ⟨faceImage f.val (collarFace (K := K) colour v).property,
    faceImage_mem f.property (collarFace (K := K) colour v).property⟩
  monotone' := fun a b h => faceImage_mono f.val (collarFace (K := K) colour a).property
    (collarFace (K := K) colour b).property ((collarFace (K := K) colour).monotone h)

private def liftSecond (colour : X → Bool) (f : SimplicialSecondMap (K := K) colour) :
    Vertex (collarComplex K colour) → Vertex (sd (sd (sd K))) :=
  mapCollar (fun v => decide (inTwoCutCollar colour v)) (liftSecondOrder (K := K) colour f)

private theorem lift_second_step [Finite (Face (sd K))] (colour : X → Bool)
    (f g : SimplicialSecondMap (K := K) colour) (h : Contiguous f.val g.val) :
    ReflTransGen Contiguous (liftSecond (K := K) colour f) (liftSecond (K := K) colour g) := by
  let F := liftSecondOrder (K := K) colour f
  let G := liftSecondOrder (K := K) colour g
  let top : {v : Face (sd (sd K)) // decide (inTwoCutCollar colour v) = true} →o
      Face (sd (sd K)) := {
    toFun v := ⟨(F v).val ∪ (G v).val, h _ (collarFace colour v).property⟩
    monotone' := fun _ _ hab => Finset.union_subset_union (F.monotone hab) (G.monotone hab) }
  exact (collar_chain_symm (descending_collar_maps _ top F
    (fun _ => Finset.subset_union_left))).trans
    (descending_collar_maps _ top G (fun _ => Finset.subset_union_right))

private theorem lift_second_chain [Finite (Face (sd K))] (colour : X → Bool)
    (f g : SimplicialSecondMap (K := K) colour) (h : ReflTransGen Contiguous f.val g.val) :
    ReflTransGen Contiguous (liftSecond (K := K) colour f) (liftSecond (K := K) colour g) := by
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  have chain {g' : SecondVertexMap (K := K) colour} (hgchain : ReflTransGen Contiguous f g') :
      ∀ hg' : Contiguous g' g', ReflTransGen Contiguous
        (liftSecond (K := K) colour ⟨f, hf⟩) (liftSecond (K := K) colour ⟨g', hg'⟩) := by
    induction hgchain with
    | refl => exact fun _ => .refl
    | @tail b c _ hstep ih =>
      intro hg'
      have hprior : Contiguous b b := by
        intro s hs
        rw [Finset.union_idempotent]
        exact ((sd (sd K)).isRelLowerSet_faces (hstep s hs)).2
          Finset.subset_union_left (hs.1.1.attach.image _)
      exact (ih hprior).trans (lift_second_step colour ⟨b, hprior⟩ ⟨c, hg'⟩ hstep)
  exact chain h hg

private theorem map_collar_simplicial (p : Face K → Bool)
    (f : {v : Face K // p v = true} →o Face L) :
    Contiguous (mapCollar p f) (mapCollar p f) := by
  intro s hs
  rw [Finset.union_idempotent]
  refine ⟨hs.1.1.attach.image _, ?_, fun a _ => a.property⟩
  intro a ha b hb hne
  obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff (mapCollar p f) hs a).mp ha
  obtain ⟨y, hy, rfl⟩ := (mem_faceImage_iff (mapCollar p f) hs b).mp hb
  rcases hs.1.2.1 hx hy (fun h => hne (congrArg f (Subtype.ext h))) with h | h
  · exact Or.inl (lt_of_le_of_ne (f.monotone h.le) hne)
  · exact Or.inr (lt_of_le_of_ne (f.monotone h.le) hne.symm)

private theorem liftSecond_mapCollar_image (colour : X → Bool)
    (f : SurvivingFlag (K := K) colour →o Face (sd K)) (v : Vertex (collarComplex K colour)) :
    let p := survivesSecond (K := K) colour
    (liftSecond colour ⟨mapCollar p f, map_collar_simplicial p f⟩ v).val.val =
      (v.val.val.subtype (fun b => survivesSecond (K := K) colour b = true)).image f := by
  intro p
  ext b
  change b ∈ faceImage (mapCollar (survivesSecond (K := K) colour) f)
    (collarFace (K := K) colour (vertexIn v)).property ↔ _
  rw [mem_faceImage_iff, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨vertexIn a, Finset.mem_subtype.mpr ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    have ha' := Finset.mem_subtype.mp ha
    let u : Vertex (colourComplex (sd (sd K)) (survivesSecond (K := K) colour)) :=
      ⟨a.val, (vertexOfFace (sd K) a.val).property, fun b hb => by
        rw [Finset.mem_singleton.mp hb]
        exact a.property⟩
    exact ⟨u, ha', rfl⟩

/-- The inclusion of the two-cut collar and its actual iterated retraction
into the ambient third subdivision belong to the same contiguity class. -/
theorem collar_inclusion_contiguous [Finite X] [Finite (Face K)] [Finite (Face (sd K))]
    (colour : X → Bool) :
    ReflTransGen Contiguous
      (fun v : Vertex (collarComplex K colour) => ⟨v.val, v.property.1⟩)
      (fun v => vertexOfFace (sd (sd K))
        ((forgetColour (K := K) colour 3).val (retract colour (collarVertex colour v)))) := by
  let p := survivesSecond (K := K) colour
  let f := survivingInclusion (K := K) colour
  let g := liftFirst (K := K) colour (cutInAmbient (K := K) colour)
  have H := lift_second_chain colour
    ⟨mapCollar p f, map_collar_simplicial _ _⟩ ⟨mapCollar p g, map_collar_simplicial _ _⟩
    ((trim_second_contiguous colour).trans (lift_first_contiguous colour))
  convert H using 1
  · funext v
    apply Subtype.ext
    apply Subtype.ext
    rw [liftSecond_mapCollar_image]
    ext b
    simp only [Finset.mem_image, Finset.mem_subtype]
    exact ⟨fun hb => ⟨⟨b, decide_eq_true ((collarVertex colour v).property b hb)⟩, hb, rfl⟩,
      fun ⟨a, ha, e⟩ => e ▸ ha⟩
  · funext v
    apply Subtype.ext
    apply Subtype.ext
    rw [liftSecond_mapCollar_image]
    change (((v.val.val.subtype fun b => (cutFlag colour b).Nonempty).image (second colour)).image
      (forgetColour (K := K) colour 2).val) = _
    rw [Finset.image_image]
    ext b
    simp only [Finset.mem_image, Finset.mem_subtype, Function.comp_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      let a' : SurvivingFlag (K := K) colour := ⟨a.val, decide_eq_true a.property⟩
      exact ⟨a', ha, liftFirst_cut_eq colour a'⟩
    · rintro ⟨a, ha, rfl⟩
      let a' : {b : Face (sd K) // (cutFlag colour b).Nonempty} :=
        ⟨a.val, of_decide_eq_true a.property⟩
      exact ⟨a', ha, (liftFirst_cut_eq colour a).symm⟩

end

end D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
