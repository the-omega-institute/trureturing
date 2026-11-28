/- GID: D5/S3/Topology/StableCategory/MixedSimplexAttachment
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/MixedSimplexAttachment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A mixed simplex attachment admits categorical transport with exact old intersections. -/

import D5.S3.Topology.StableCategory.MixedSimplexChart
import D5.S3.Topology.StableCategory.ExactCategoricalExtension

/-! Relative contiguity gluing and exact ordinary subdivision transfer
for the mixed simplex attachment in Question 6.3. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.MixedSimplexAttachment

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd)
open BarycentricNeighborhoodIteration (FullIn iteratedAmbient iteratedSubcomplex
  subdivision subdivision_full)
open ExactCategoricalExtension (CategoricalIn exact_extension_of_full_cover)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem mem_iteratedSubcomplex_iff)
open MixedSimplexChart (simplex horn Tau chart hornSubdivision hornSubdivision_le_chart
  chart_full chart_retracts_rel_horn retraction retraction_simplicial retraction_fixes_horn
  fold fold_simplicial foldTwice piece mixed_block_cover)
open OrdinaryCollarNaturality (pullback)
open OrdinaryContiguityLift (Simplicial includeSubcomplex include_subcomplex_simplicial
  ofTotal of_total_simplicial comp_chains comp_image iterate_comp lift_iterates)
open OrdinarySubdivisionMap (iterate originalSupport_image)
open Relation (ReflTransGen)
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private ofTotal_faceImage from D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private face_image_comp face_image_include face_image_restrict id_simplicial from
  D5.S3.Topology.StableCategory.FourPieceCategoricalCover
open private categorical_of_subdivision_le subdivision_mono from
  D5.S3.Topology.StableCategory.ExactCategoricalExtension

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {X Y : Type}

private theorem vertex_mem {J : PreAbstractSimplicialComplex X} {s : Finset X}
    (hs : s ∈ J) {x : X} (hx : x ∈ s) : ({x} : Finset X) ∈ J :=
  (J.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx)
    (Finset.singleton_nonempty x)

private theorem image_mem_map {B : PreAbstractSimplicialComplex X} (e : X → Y)
    {s : Finset X} (hs : s ∈ B) : image s e ∈ B.map e := ⟨s, hs, rfl⟩

private theorem image_mem_map_iff {B : PreAbstractSimplicialComplex X} {e : X → Y}
    (he : Function.Injective e) {s : Finset X} : image s e ∈ B.map e ↔ s ∈ B := by
  constructor
  · rintro ⟨t, ht, hts⟩
    exact (Finset.image_injective he hts) ▸ ht
  · exact image_mem_map e

private theorem map_le_of_image {B : PreAbstractSimplicialComplex X}
    {J : PreAbstractSimplicialComplex Y} (e : X → Y)
    (h : ∀ s ∈ B, image s e ∈ J) : B.map e ≤ J := by
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

private theorem exists_map_vertex {B : PreAbstractSimplicialComplex X} (e : X → Y)
    (v : Vertex (B.map e)) : ∃ u : Vertex B, e u.val = v.val := by
  obtain ⟨s, hs, he⟩ := v.property
  obtain ⟨x, hx⟩ := (B.isRelLowerSet_faces hs).1
  have hm : e x ∈ ({v.val} : Finset Y) := he ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
  exact ⟨⟨x, vertex_mem hs hx⟩, Finset.mem_singleton.mp hm⟩

private def unmap {B : PreAbstractSimplicialComplex X} (e : X → Y)
    (v : Vertex (B.map e)) : Vertex B :=
  (exists_map_vertex e v).choose

private theorem unmap_val {B : PreAbstractSimplicialComplex X} (e : X → Y)
    (v : Vertex (B.map e)) : e (unmap e v).val = v.val :=
  (exists_map_vertex e v).choose_spec

private theorem unmap_simplicial {B : PreAbstractSimplicialComplex X} {e : X → Y}
    (he : Function.Injective e) : Simplicial (unmap (B := B) e) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hEq : faceImage (unmap (B := B) e) (image_mem_map e ht) = t := by
    ext x
    rw [mem_faceImage_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
      exact (he (hyv.trans (unmap_val e v).symm)) ▸ hy
    · intro hx
      let v : Vertex (B.map e) := ⟨e x, vertex_mem (image_mem_map e ht)
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
      exact ⟨v, Finset.mem_image.mpr ⟨x, hx, rfl⟩, he (unmap_val e v)⟩
  rwa [hEq]

section RelativeGluing

variable {P : PreAbstractSimplicialComplex Y} {B : PreAbstractSimplicialComplex X}
variable (e : X → Y)

private def chartInUnion : Vertex B → Vertex (P ⊔ B.map e) :=
  ofTotal e (fun _ hs => Or.inr (image_mem_map e hs))

private def extend (f : Vertex B → Vertex B) (v : Vertex (P ⊔ B.map e)) :
    Vertex (P ⊔ B.map e) :=
  if hp : {v.val} ∈ P then v
  else chartInUnion e (f (unmap e ⟨v.val, v.property.resolve_left hp⟩))

private theorem extend_chart (he : Function.Injective e) {f : Vertex B → Vertex B}
    (hfix : ∀ v : Vertex B, {e v.val} ∈ P → f v = v) :
    extend e f ∘ chartInUnion e = chartInUnion e (P := P) ∘ f := by
  funext v
  change extend e f (chartInUnion e v) = chartInUnion e (f v)
  by_cases hv : {e v.val} ∈ P
  · rw [hfix v hv]
    exact dite_eq_left hv
  · unfold extend
    have hv' : {(chartInUnion e (P := P) v).val} ∉ P := hv
    rw [dite_eq_right hv']
    apply congrArg (chartInUnion e (P := P) ∘ f)
    apply Subtype.ext
    apply he
    exact unmap_val e _

private theorem extend_face_old (f : Vertex B → Vertex B) {s : Finset Y} (hs : s ∈ P) :
    faceImage (extend e (P := P) f) (show s ∈ P ⊔ B.map e from Or.inl hs) = s := by
  let j : Vertex P → Vertex (P ⊔ B.map e) := includeSubcomplex le_sup_left
  have hj : faceImage j hs = s := face_image_include _ _ hs
  have eq : extend e f ∘ j = j := by
    funext v
    exact dite_eq_left v.property
  exact (face_image_restrict le_sup_left (extend e f) s hs).symm.trans
    ((congrArg (fun k => faceImage k hs) eq).trans hj)

private theorem face_image_eq_of_eq {U W : Type}
    {J : PreAbstractSimplicialComplex U} {Q : PreAbstractSimplicialComplex W}
    (f : Vertex J → Vertex Q) {s t : Finset U} (h : s = t)
    (hs : s ∈ J) (ht : t ∈ J) : faceImage f hs = faceImage f ht := by
  subst t
  rfl

private theorem extend_face_chart (he : Function.Injective e) {f : Vertex B → Vertex B}
    (hf : ∀ v : Vertex B, {e v.val} ∈ P → f v = v)
    {s : Finset X} (hs : s ∈ B) (hfs : faceImage f hs ∈ B) :
    faceImage (extend e (P := P) f) (show image s e ∈ P ⊔ B.map e from
      Or.inr (image_mem_map e hs)) = image (faceImage f hs) e := by
  let j : Vertex B → Vertex (P ⊔ B.map e) := chartInUnion e
  have hj : faceImage j hs = image s e := ofTotal_faceImage _ _ _ hs
  have hj' : Simplicial j := of_total_simplicial e (fun _ hb => Or.inr (image_mem_map e hb))
  have h : faceImage (extend e f ∘ j) hs = faceImage (extend e f) (hj' s hs) :=
    face_image_comp j _ s hs _
  rw [show extend e f ∘ j = j ∘ f from extend_chart e he hf,
    face_image_comp f j s hs hfs] at h
  change faceImage (chartInUnion e) hfs = _ at h
  unfold chartInUnion at h
  rw [ofTotal_faceImage] at h
  exact (face_image_eq_of_eq (extend e f) hj _ _).symm.trans h.symm

private theorem extend_step (he : Function.Injective e)
    {f g : Vertex B → Vertex B} (hfg : Contiguous f g)
    (hf : ∀ v : Vertex B, {e v.val} ∈ P → f v = v)
    (hg : ∀ v : Vertex B, {e v.val} ∈ P → g v = v) :
    Contiguous (extend e (P := P) f) (extend e g) := by
  intro s hs
  rcases (show s ∈ P ∨ s ∈ B.map e from hs) with hp | ⟨t, ht, rfl⟩
  · rw [extend_face_old e f hp, extend_face_old e g hp, Finset.union_idempotent]
    exact Or.inl hp
  · have hm := B.isRelLowerSet_faces (hfg t ht)
    have hf' := hm.2 Finset.subset_union_left ((B.isRelLowerSet_faces ht).1.attach.image _)
    have hg' := hm.2 Finset.subset_union_right ((B.isRelLowerSet_faces ht).1.attach.image _)
    rw [extend_face_chart e he hf ht hf', extend_face_chart e he hg ht hg',
      ← Finset.image_union]
    exact Or.inr (image_mem_map e (hfg t ht))

/-- A chart chain that fixes the overlap extends by the identity on the
other summand. The glued endpoint factors through that summand whenever
the chart endpoint takes its embedded values there. -/
theorem glue_relative_chain (he : Function.Injective e)
    (f : Vertex B → Vertex B) (hf : Simplicial f)
    (hfix : ∀ v : Vertex B, {e v.val} ∈ P → f v = v)
    (hland : ∀ s (hs : s ∈ B), image (faceImage f hs) e ∈ P)
    (h : ReflTransGen (fun g k : Vertex B → Vertex B =>
      Contiguous g k ∧ ∀ v : Vertex B, {e v.val} ∈ P → g v = v ∧ k v = v) id f) :
    let R := P ⊔ B.map e
    ∃ r : Vertex R → Vertex P, Simplicial r ∧
      (∀ v : Vertex P, r (includeSubcomplex (show P ≤ R from le_sup_left) v) = v) ∧
      ReflTransGen (fun g k : Vertex R → Vertex R =>
        Contiguous g k ∧ ∀ v : Vertex P,
          let j := includeSubcomplex (show P ≤ R from le_sup_left) v
          g j = j ∧ k j = j) id
        (includeSubcomplex (show P ≤ R from le_sup_left) ∘ r) := by
  intro R
  have hstart : extend e (P := P) (id : Vertex B → Vertex B) = id := by
    funext v
    by_cases hv : {v.val} ∈ P
    · exact dite_eq_left hv
    · unfold extend
      rw [dite_eq_right hv]
      exact Subtype.ext (unmap_val e _)
  have hP (v : Vertex R) : {(extend e f v).val} ∈ P := by
    by_cases hv : {v.val} ∈ P
    · simpa only [extend, dite_eq_left hv] using hv
    · rw [extend, dite_eq_right hv]
      have hm := hland _ (unmap e ⟨v.val, v.property.resolve_left hv⟩).property
      change {e (f (unmap e ⟨v.val, v.property.resolve_left hv⟩)).val} ∈ P
      simpa only [GraphSubdivisionIntervals.faceImage_singleton, image, Finset.image_singleton]
        using hm
  let r (v : Vertex R) : Vertex P := ⟨(extend e f v).val, hP v⟩
  have hend : extend e f = includeSubcomplex (show P ≤ R from le_sup_left) ∘ r := by
    funext v
    exact Subtype.ext rfl
  refine ⟨r, ?_, ?_, ?_⟩
  · intro s hs
    change faceImage (extend e f) hs ∈ P
    rcases (show s ∈ P ∨ s ∈ B.map e from hs) with hp | ⟨t, ht, rfl⟩
    · rwa [extend_face_old e f hp]
    · rw [extend_face_chart e he hfix ht (hf t ht)]
      exact hland t ht
  · intro v
    apply Subtype.ext
    change (extend e f (includeSubcomplex (show P ≤ R from le_sup_left) v)).val = v.val
    simp only [extend, dite_eq_left v.property, includeSubcomplex]
  · let rel (g k : Vertex R → Vertex R) :=
      Contiguous g k ∧ ∀ v : Vertex P,
        let j := includeSubcomplex (show P ≤ R from le_sup_left) v
        g j = j ∧ k j = j
    have lifted : ReflTransGen rel (extend e (P := P) id) (extend e f) :=
      ReflTransGen.lift (extend e (P := P)) (by
        intro g k hgk
        exact ⟨extend_step e he hgk.1 (fun v hv => (hgk.2 v hv).1)
          (fun v hv => (hgk.2 v hv).2), fun v => ⟨dite_eq_left v.property, dite_eq_left v.property⟩⟩)
        _ _ h
    rw [hstart, hend] at lifted
    exact lifted

end RelativeGluing

section SubdivisionEmbeddings

variable {B : PreAbstractSimplicialComplex X} {J : PreAbstractSimplicialComplex Y}

private theorem identity_image {P K : PreAbstractSimplicialComplex X} (h : P ≤ K) :
    ∀ s ∈ P, image s id ∈ K := by
  intro s hs
  simpa only [image, Finset.image_id] using (show s ∈ K from h hs)

private abbrev emb {P K : PreAbstractSimplicialComplex X} (h : P ≤ K) (n : ℕ) :=
  (iterate id (identity_image h) n).val

private theorem iterate_injective (f : X → Y) (hf : ∀ s ∈ B, image s f ∈ J)
    (h : Function.Injective f) (n : ℕ) :
    Function.Injective (iterate f hf n).val := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro u v huv
    apply Subtype.ext
    exact Finset.image_injective ih (congrArg Subtype.val huv)

private theorem emb_injective {P K : PreAbstractSimplicialComplex X} (h : P ≤ K) (n : ℕ) :
    Function.Injective (emb h n) :=
  iterate_injective id (identity_image h) (fun _ _ hx => hx) n

private theorem map_sd (f : X → Y) (hf : ∀ s ∈ B, image s f ∈ J)
    (hinj : Function.Injective f) :
    (sd B).map (iterate f hf 1).val = subdivision J (B.map f) := by
  let e := (iterate f hf 1).val
  have e_inj : Function.Injective e := iterate_injective f hf hinj 1
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩
    have hm := (iterate f hf 1).property t ht
    refine ⟨hm.1, hm.2.1, ?_⟩
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact image_mem_map f p.property
  · intro s hs
    have preimage (q : Face J) (hq : q ∈ s) : ∃ p : Face B, e p = q := by
      obtain ⟨t, ht, he⟩ := hs.2.2 q hq
      exact ⟨⟨t, ht⟩, Subtype.ext he⟩
    let t := s.attach.image fun q => (preimage q.val q.property).choose
    have hts : image t e = s := by
      calc
        image t e = s.attach.image Subtype.val := by
          change (s.attach.image _).image e = _
          rw [Finset.image_image]
          apply Finset.image_congr
          intro q _
          exact (preimage q.val q.property).choose_spec
        _ = s := Finset.attach_image_val
    refine ⟨t, ⟨?_, ?_, fun p _ => p.property⟩, hts⟩
    · exact hs.1.attach.image _
    · intro p hp q hq hpq
      have hmem (u : Face B) (hu : u ∈ t) : e u ∈ s :=
        hts ▸ Finset.mem_image.mpr ⟨u, hu, rfl⟩
      rcases hs.2.1 (hmem p hp) (hmem q hq) (fun he => hpq (e_inj he)) with h | h
      · exact Or.inl (lt_of_le_of_ne ((Finset.image_subset_image_iff hinj).mp h.le) hpq)
      · exact Or.inr (lt_of_le_of_ne ((Finset.image_subset_image_iff hinj).mp h.le) hpq.symm)

private theorem map_emb {P K : PreAbstractSimplicialComplex X} (h : P ≤ K) (n : ℕ) :
    (iteratedAmbient P n).2.map (emb h n) = iteratedSubcomplex K P n := by
  induction n with
  | zero =>
    exact le_antisymm (map_le_of_image id (identity_image (le_refl P))) (by
      intro s hs
      exact ⟨s, hs, Finset.image_id⟩)
  | succ n ih =>
    change (sd (iteratedAmbient P n).2).map
        (iterate (emb h n) (iterate id (identity_image h) n).property 1).val =
      subdivision (iteratedAmbient K n).2 (iteratedSubcomplex K P n)
    rw [map_sd _ _ (emb_injective h n), ih]

private theorem iterate_agree {P : PreAbstractSimplicialComplex X} {K : PreAbstractSimplicialComplex Y}
    {f g : X → Y} (hf : ∀ s ∈ P, image s f ∈ K) (hg : ∀ s ∈ P, image s g ∈ K)
    (h : ∀ x : Vertex P, f x.val = g x.val) (n : ℕ) :
    ∀ u : Vertex (iteratedAmbient P n).2,
      (iterate f hf n).val u.val = (iterate g hg n).val u.val := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro u
    apply Subtype.ext
    apply Finset.image_congr
    intro x hx
    exact ih ⟨x, vertex_mem u.val.property hx⟩

private theorem map_full {B₀ B₁ : PreAbstractSimplicialComplex X} {e : X → Y}
    (he : Function.Injective e) (h : FullIn B₀ B₁) : FullIn (B₀.map e) (B₁.map e) := by
  refine ⟨map_le_of_image e (fun _ hs => image_mem_map e (h.1 hs)), ?_⟩
  intro s hs
  obtain ⟨t, ht, heq⟩ := s.property
  have ht' : t ∈ B₀ := h.2 ⟨t, ht⟩ (by
    intro x hx
    apply (image_mem_map_iff he).mp
    rw [image, Finset.image_singleton]
    exact hs (e x) (heq ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  exact ⟨t, ht', heq⟩

private theorem full_trans {B₀ B₁ B₂ : PreAbstractSimplicialComplex X}
    (h₀ : FullIn B₀ B₁) (h₁ : FullIn B₁ B₂) : FullIn B₀ B₂ := by
  refine ⟨h₀.1.trans h₁.1, ?_⟩
  intro s hs
  exact h₀.2 ⟨s.val, h₁.2 s (fun x hx => h₀.1 (hs x hx))⟩ hs

private theorem full_union {P W U : PreAbstractSimplicialComplex X}
    (hW : FullIn W U) (hmeet : P ⊓ U ≤ W) :
    FullIn (P ⊔ W) (P ⊔ U) := by
  refine ⟨sup_le le_sup_left (hW.1.trans le_sup_right), ?_⟩
  intro s hs
  rcases (show s.val ∈ P ∨ s.val ∈ U from s.property) with hp | hu
  · exact Or.inl hp
  · refine Or.inr (hW.2 ⟨s.val, hu⟩ (fun x hx => ?_))
    exact (show {x} ∈ P ∨ {x} ∈ W from hs x hx).elim
      (fun hxP => hmeet ⟨hxP, vertex_mem hu hx⟩) id

end SubdivisionEmbeddings

section Attachment

variable {V : Type}
variable {K A P : PreAbstractSimplicialComplex V} {S L : Finset V} {a : V}

private abbrev D2 (K P : PreAbstractSimplicialComplex V) := iteratedSubcomplex K P 2

private theorem d2_le (K : PreAbstractSimplicialComplex V) {P Q : PreAbstractSimplicialComplex V}
    (h : P ≤ Q) : D2 K P ≤ D2 K Q :=
  subdivision_mono (sd K) (subdivision_mono K h)

private theorem d2_sup (K P Q : PreAbstractSimplicialComplex V) :
    D2 K (P ⊔ Q) = D2 K P ⊔ D2 K Q := by
  refine le_antisymm ?_ (sup_le (d2_le K le_sup_left) (d2_le K le_sup_right))
  intro s hs
  have h := (mem_iteratedSubcomplex_iff 2 ((subdivision_full (sd K) _).1 hs)).mp hs
  have hamb : s ∈ sd (sd K) := (subdivision_full (sd K) _).1 hs
  exact (show _ ∈ P ∨ _ ∈ Q from h).imp
    (mem_iteratedSubcomplex_iff 2 hamb).mpr (mem_iteratedSubcomplex_iff 2 hamb).mpr

private theorem tau_le_simplex (ha : a ∈ S) (hL : L ⊆ S) : Tau a L ≤ simplex S :=
  fun _ hs => ⟨hs.1, hs.2.trans (Finset.insert_subset_iff.mpr ⟨ha, hL⟩)⟩

private theorem old_tau_meets_horn (ha : a ∈ S) (hL : L ⊆ S)
    (hmissing : ∀ s ∈ P, s ∈ simplex S → ¬ L ⊆ s) : P ⊓ Tau a L ≤ horn a L :=
  fun s hs => ⟨hs.2, hmissing s hs.1 (tau_le_simplex ha hL hs.2)⟩

/-- Extend the block fold to the old region and the attaching simplex. -/
private def collapse (S : Finset V) (a : V) (L : Finset V) (x : V) :=
  if x ∈ S then fold a L x else x

private theorem collapse_on_simplex {s : Finset V} (hs : s ∈ simplex S) :
    image s (collapse S a L) = image s (fold a L) :=
  Finset.image_congr (fun x hx => ite_eq_left (hs.2 hx))

private theorem collapse_on_exterior
    (hext : ∀ s ∈ P, s ∉ simplex S → ∀ x ∈ s, x ∈ S → x ∈ insert a L)
    {s : Finset V} (hs : s ∈ P) (hn : s ∉ simplex S) :
    image s (collapse S a L) = s := by
  calc
    image s (collapse S a L) = image s id := by
      apply Finset.image_congr
      intro x hx
      by_cases hS : x ∈ S
      · rw [collapse, ite_eq_left hS]
        rcases Finset.mem_insert.mp (hext s hs hn x hx hS) with rfl | hL
        · simp [fold]
        · exact ite_eq_left hL
      · exact ite_eq_right hS
    _ = s := Finset.image_id

private theorem collapse_old (ha : a ∉ L) (hH : horn a L ≤ P)
    (hmissing : ∀ s ∈ P, s ∈ simplex S → ¬ L ⊆ s)
    (hext : ∀ s ∈ P, s ∉ simplex S → ∀ x ∈ s, x ∈ S → x ∈ insert a L) :
    ∀ s ∈ P, image s (collapse S a L) ∈ P := by
  intro s hs
  by_cases hσ : s ∈ simplex S
  · rw [collapse_on_simplex hσ]
    apply hH
    refine ⟨fold_simplicial S a L s hσ, fun h => hmissing s hs hσ (fun x hx => ?_)⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp (h hx)
    by_cases hyL : y ∈ L
    · simp only [fold, ite_eq_left hyL] at he
      exact he ▸ hy
    · rw [fold, ite_eq_right hyL] at he
      exact (ha (he.symm ▸ hx)).elim
  · rwa [collapse_on_exterior hext hs hσ]

private theorem collapse_image (ha : a ∉ L) (hH : horn a L ≤ P)
    (hmissing : ∀ s ∈ P, s ∈ simplex S → ¬ L ⊆ s)
    (hext : ∀ s ∈ P, s ∉ simplex S → ∀ x ∈ s, x ∈ S → x ∈ insert a L) :
    ∀ s ∈ P ⊔ simplex S, image s (collapse S a L) ∈ P ⊔ Tau a L := by
  intro s hs
  rcases (show s ∈ P ∨ s ∈ simplex S from hs) with hp | hσ
  · exact Or.inl (collapse_old ha hH hmissing hext s hp)
  · rw [collapse_on_simplex hσ]
    exact Or.inr (fold_simplicial S a L s hσ)

private theorem collapse_contiguous (hP : P ≤ K) (hS : simplex S ≤ K)
    (ha : a ∈ S) (hL : L ⊆ S)
    (hext : ∀ s ∈ P, s ∉ simplex S → ∀ x ∈ s, x ∈ S → x ∈ insert a L)
    (hf : ∀ s ∈ P ⊔ simplex S, image s (collapse S a L) ∈ K) :
    Contiguous (ofTotal id (identity_image (sup_le hP hS)))
      (ofTotal (collapse S a L) hf) := by
  intro s hs
  rw [ofTotal_faceImage, ofTotal_faceImage]
  have hid : image s id = s := Finset.image_id
  rw [hid]
  by_cases hσ : s ∈ simplex S
  · apply hS
    rw [collapse_on_simplex hσ]
    exact ⟨hσ.1.mono Finset.subset_union_left, Finset.union_subset hσ.2
      ((tau_le_simplex ha hL (fold_simplicial S a L s hσ)).2)⟩
  · have hp := (show s ∈ P ∨ s ∈ simplex S from hs).resolve_right hσ
    rw [collapse_on_exterior hext hp hσ, Finset.union_idempotent]
    exact hP hp

private theorem emb_support {J K : PreAbstractSimplicialComplex V} (h : J ≤ K)
    (s : Finset (Face (sd J))) :
    originalSupport K 2 (image s (emb h 2)) = originalSupport J 2 s := by
  rw [originalSupport_image id (identity_image h) 2]
  exact Finset.image_id

private theorem chart_region [Finite V] (hP : P ≤ K) (hτ : Tau a L ≤ K)
    (haS : a ∈ S) (hLS : L ⊆ S) (ha : a ∉ L) (hL : L.Nonempty)
    (hH : horn a L ≤ P)
    (hmissing : ∀ s ∈ P, s ∈ simplex S → ¬ L ⊆ s)
    (hcat : CategoricalIn hP) :
    let e := emb hτ 2
    let R := D2 K P ⊔ (chart a L).map e
    ∃ hR : FullIn R (D2 K (P ⊔ Tau a L)), CategoricalIn
      (hR.1.trans (subdivision_full (sd K) _).1) := by
  intro e R
  let W := (chart a L).map e
  let O := D2 K P
  let H := hornSubdivision a L
  have he : Function.Injective e := emb_injective hτ 2
  have hfW : FullIn W (D2 K (Tau a L)) := by
    change FullIn W (iteratedSubcomplex K (Tau a L) 2)
    rw [← map_emb hτ 2]
    exact map_full he (chart_full a L)
  have meetHorn : ∀ s ∈ D2 K P ⊓ D2 K (Tau a L), s ∈ D2 K (horn a L) := by
    intro s hs
    have hamb : s ∈ sd (sd K) := (subdivision_full (sd K) _).1 hs.1
    apply (mem_iteratedSubcomplex_iff 2 hamb).mpr
    exact old_tau_meets_horn haS hLS hmissing
      ⟨(mem_iteratedSubcomplex_iff 2 hamb).mp hs.1, (mem_iteratedSubcomplex_iff 2 hamb).mp hs.2⟩
  have hornImage : ∀ s ∈ H, image s e ∈ O := by
    intro s hs
    have hs' : s ∈ sd (sd (Tau a L)) := (subdivision_full (sd (Tau a L)) _).1 hs
    have ht : image s e ∈ sd (sd K) := (iterate id (identity_image hτ) 2).property s hs'
    apply (mem_iteratedSubcomplex_iff 2 ht).mpr
    rw [emb_support hτ s]
    exact hH ((mem_iteratedSubcomplex_iff 2 hs').mp hs)
  have overlap (v : Vertex (chart a L)) (hv : {e v.val} ∈ O) : {v.val} ∈ H := by
    have hv' : {v.val} ∈ sd (sd (Tau a L)) := (chart_full a L).1 v.property
    apply (mem_iteratedSubcomplex_iff 2 hv').mpr
    have hτv : {e v.val} ∈ D2 K (Tau a L) := hfW.1 (by
      change {e v.val} ∈ (chart a L).map e
      simpa only [image, Finset.image_singleton] using image_mem_map e v.property)
    have hh := (mem_iteratedSubcomplex_iff 2 ((subdivision_full (sd K) _).1 hv)).mp
      (meetHorn _ ⟨hv, hτv⟩)
    have h : originalSupport K 2 (image {v.val} e) ∈ horn a L := by
      simpa only [Finset.image_singleton] using hh
    rwa [emb_support hτ] at h
  have hmeet : O ⊓ D2 K (Tau a L) ≤ W := by
    intro s hs
    have hsτ : s ∈ iteratedSubcomplex K (Tau a L) 2 := hs.2
    rw [← map_emb hτ 2] at hsτ
    obtain ⟨t, ht, heq⟩ := hsτ
    have h := meetHorn s hs
    have hamb : s ∈ sd (sd K) := (subdivision_full (sd K) _).1 hs.1
    have hsup := (mem_iteratedSubcomplex_iff 2 hamb).mp h
    rw [← heq, emb_support hτ] at hsup
    exact ⟨t, hornSubdivision_le_chart a L ((mem_iteratedSubcomplex_iff 2 ht).mpr hsup), heq⟩
  have hR : FullIn R (D2 K (P ⊔ Tau a L)) := by
    rw [d2_sup]
    exact full_union hfW hmeet
  let f := includeSubcomplex (hornSubdivision_le_chart a L) ∘ retraction ha hL
  have hf : Simplicial f :=
    (include_subcomplex_simplicial _).comp (retraction_simplicial ha hL)
  have hfix (v : Vertex (chart a L)) (hv : {e v.val} ∈ O) : f v = v := by
    let u : Vertex H := ⟨v.val, overlap v hv⟩
    have hu : includeSubcomplex (hornSubdivision_le_chart a L) u = v := Subtype.ext rfl
    rw [← hu]
    exact congrArg (includeSubcomplex (hornSubdivision_le_chart a L))
      (retraction_fixes_horn ha hL u)
  have hland (s : Finset (Face (sd (Tau a L)))) (hs : s ∈ chart a L) :
      image (faceImage f hs) e ∈ O :=
    hornImage _ (retraction_simplicial ha hL s hs)
  have hchain : ReflTransGen (fun g k : Vertex (chart a L) → Vertex (chart a L) =>
      Contiguous g k ∧ ∀ v, {e v.val} ∈ O → g v = v ∧ k v = v) id f :=
    ReflTransGen.lift id (by
      intro g k h
      refine ⟨h.1, fun v hv => ?_⟩
      let u : Vertex H := ⟨v.val, overlap v hv⟩
      have hu : includeSubcomplex (hornSubdivision_le_chart a L) u = v := Subtype.ext rfl
      simpa only [Function.id_def, hu] using h.2 u) _ _ (chart_retracts_rel_horn ha hL)
  obtain ⟨r, hr, _, hrel⟩ := glue_relative_chain (P := O) e he f hf hfix hland hchain
  have hglue : ReflTransGen Contiguous id (includeSubcomplex (show O ≤ R from le_sup_left) ∘ r) :=
    ReflTransGen.lift id (fun _ _ h => h.1) _ _ hrel
  let hRK : R ≤ sd (sd K) := hR.1.trans (subdivision_full (sd K) _).1
  let hOK : O ≤ sd (sd K) := (subdivision_full (sd K) _).1
  letI : Finite (iteratedAmbient K 1).fst := inferInstanceAs (Finite (Face K))
  have hO : CategoricalIn hOK := categorical_of_subdivision_le
    (le_refl O) (subdivision_full K P).1
    (categorical_of_subdivision_le (le_refl (subdivision K P)) hP hcat)
  obtain ⟨c, hc⟩ := hO
  have hg := comp_chains id (includeSubcomplex hRK) id_simplicial
    (include_subcomplex_simplicial hRK) hglue
  have hfinish := comp_chains r id hr id_simplicial hc
  refine ⟨hR, c, ?_⟩
  exact hg.trans hfinish

private theorem pullback_full {U W : Type} {J : PreAbstractSimplicialComplex U}
    {Q R : PreAbstractSimplicialComplex W} {f : U → W}
    (hf : ∀ s ∈ J, image s f ∈ Q) (hR : FullIn R Q) :
    FullIn (pullback J f R) J := by
  refine ⟨fun _ hs => hs.1, ?_⟩
  intro s hs
  refine ⟨s.property, hR.2 ⟨image s.val f, hf s.val s.property⟩ (fun y hy => ?_)⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  simpa only [Finset.image_singleton] using (hs x hx).2

/-- The full categorical pullback for one colour in the second ordinary
subdivision. It contains the old colour and the embedded simplex chart piece. -/
theorem mixed_region [Finite V] (hP : P ≤ K) (hS : simplex S ≤ K)
    (haS : a ∈ S) (hLS : L ⊆ S) (ha : a ∉ L) (hL : L.Nonempty)
    (hH : horn a L ≤ P)
    (hmissing : ∀ s ∈ P, s ∈ simplex S → ¬ L ⊆ s)
    (hext : ∀ s ∈ P, s ∉ simplex S → ∀ x ∈ s, x ∈ S → x ∈ insert a L)
    (hcat : CategoricalIn hP) :
    ∃ Z : PreAbstractSimplicialComplex (Face (sd K)),
      ∃ hZ : FullIn Z (sd (sd K)),
        D2 K P ≤ Z ∧ (piece S a L).map (emb hS 2) ≤ Z ∧ CategoricalIn hZ.1 := by
  let E := P ⊔ simplex S
  let hE : E ≤ K := sup_le hP hS
  let hSE : simplex S ≤ E := le_sup_right
  let hPE : P ≤ E := le_sup_left
  let τ := Tau a L
  let hτ : τ ≤ K := (tau_le_simplex haS hLS).trans hS
  let R := D2 K P ⊔ (chart a L).map (emb hτ 2)
  obtain ⟨hR, c, hc⟩ := chart_region hP hτ haS hLS ha hL hH hmissing hcat
  let T := D2 K (P ⊔ τ)
  let hPT : P ⊔ τ ≤ K := sup_le hP hτ
  let f := collapse S a L
  have hf : ∀ s ∈ E, image s f ∈ K :=
    fun s hs => hPT (collapse_image ha hH hmissing hext s hs)
  let f₂ := (iterate f hf 2).val
  have hf₂ (s : Finset (Face (sd E))) (hs : s ∈ sd (sd E)) : image s f₂ ∈ T := by
    apply (mem_iteratedSubcomplex_iff 2 ((iterate f hf 2).property s hs)).mpr
    rw [originalSupport_image]
    exact collapse_image ha hH hmissing hext _ (originalSupport_mem 2 hs)
  let B := pullback (sd (sd E)) f₂ R
  let e := emb hE 2
  let Z := B.map e
  have hZ : FullIn Z (sd (sd K)) := by
    refine full_trans ?_ (subdivision_full (sd K) (subdivision K E))
    change FullIn Z (iteratedSubcomplex K E 2)
    rw [← map_emb hE 2]
    exact map_full (emb_injective hE 2) (pullback_full hf₂ hR)
  have hOld : D2 E P ≤ B := by
    intro s hs
    have hamb : s ∈ sd (sd E) := (subdivision_full (sd E) _).1 hs
    refine ⟨hamb, Or.inl ?_⟩
    apply (mem_iteratedSubcomplex_iff 2 ((iterate f hf 2).property s hamb)).mpr
    rw [originalSupport_image]
    exact collapse_old ha hH hmissing hext _ ((mem_iteratedSubcomplex_iff 2 hamb).mp hs)
  have foldSquare (u : Vertex (sd (sd (simplex S)))) :
      f₂ (emb hSE 2 u.val) = emb hτ 2 (foldTwice S a L u.val) := by
    have h₁ := congrFun (iterate_comp id (identity_image hSE) f hf 2) u.val
    have h₂ := congrFun (iterate_comp (fold a L) (fold_simplicial S a L)
      id (identity_image hτ) 2) u.val
    rw [← show _ = f₂ (emb hSE 2 u.val) from h₁,
      ← show _ = emb hτ 2 (foldTwice S a L u.val) from h₂]
    exact iterate_agree _ _ (fun (x : Vertex (simplex S)) =>
      ite_eq_left (Finset.singleton_subset_iff.mp x.property.2)) 2 u
  have emb_comp {J M N : PreAbstractSimplicialComplex V} (hJM : J ≤ M) (hMN : M ≤ N) :
      emb (hJM.trans hMN) 2 = emb hMN 2 ∘ emb hJM 2 :=
    iterate_comp id (identity_image hJM) id (identity_image hMN) 2
  refine ⟨Z, hZ, ?_, ?_, ?_⟩
  · intro s hs
    change s ∈ iteratedSubcomplex K P 2 at hs
    rw [← map_emb hP 2] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    refine ⟨image t (emb hPE 2), hOld ?_, ?_⟩
    · change image t (emb hPE 2) ∈ iteratedSubcomplex E P 2
      rw [← map_emb hPE 2]
      exact image_mem_map _ ht
    · simp only [image, emb_comp hPE hE, Finset.image_image]
      rfl
  · rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ sd (sd (simplex S)) := ht.1
    refine ⟨image t (emb hSE 2), ⟨(iterate id (identity_image hSE) 2).property t ht', ?_⟩, ?_⟩
    · apply Or.inr
      refine ⟨image t (foldTwice S a L), ht.2, ?_⟩
      simp only [image, Finset.image_image]
      exact Finset.image_congr (fun u hu => (foldSquare ⟨u, vertex_mem ht' hu⟩).symm)
    · simp only [image, emb_comp hSE hE, Finset.image_image]
      rfl
  · let pre : Vertex Z → Vertex B := unmap e
    have hpre : Simplicial pre := unmap_simplicial (emb_injective hE 2)
    let iB : B ≤ sd (sd E) := fun _ hs => hs.1
    let pull : Vertex B → Vertex R := ofTotal f₂ (fun _ hs => hs.2)
    have hpull : Simplicial pull := of_total_simplicial _ _
    have lifted := lift_iterates id f (identity_image hE) hf
      (ReflTransGen.single (collapse_contiguous hP hS haS hLS hext hf)) 2
    have h₁ := comp_chains (includeSubcomplex iB ∘ pre) id
      ((include_subcomplex_simplicial iB).comp hpre) id_simplicial lifted
    have h₂ := comp_chains (pull ∘ pre) id (hpull.comp hpre) id_simplicial hc
    have hstart : id ∘ ofTotal e (iterate id (identity_image hE) 2).property ∘
        (includeSubcomplex iB ∘ pre) = includeSubcomplex hZ.1 := by
      funext v
      exact Subtype.ext (unmap_val e v)
    rw [hstart] at h₁
    exact ⟨c, h₁.trans h₂⟩

/-- Both mixed regions lie in the same second ordinary subdivision of the
attachment. Their overlap with the old complex may be larger than prescribed. -/
theorem mixed_full_cover [Finite V] (P : Bool → PreAbstractSimplicialComplex V)
    (blocks : Bool → Finset V) (hK : K = A ⊔ simplex S)
    (hcover : P false ⊔ P true = A)
    (hPA : ∀ i, P i ≤ A) (haS : a ∈ S)
    (hsub : ∀ i, blocks i ⊆ S)
    (ha : ∀ i, a ∉ blocks i) (hne : ∀ i, (blocks i).Nonempty)
    (hdisj : Disjoint (blocks false) (blocks true))
    (hH : ∀ i, horn a (blocks i) ≤ P i)
    (hmissing : ∀ i s, s ∈ P i → s ∈ simplex S → ¬ blocks i ⊆ s)
    (hext : ∀ i s, s ∈ P i → s ∉ simplex S → ∀ x ∈ s, x ∈ S → x ∈ insert a (blocks i))
    (hcat : ∀ i, CategoricalIn (hPA i)) :
    ∃ Z : Bool → PreAbstractSimplicialComplex (Face (sd K)),
      ∃ hZ : ∀ i, FullIn (Z i) (sd (sd K)),
        (∀ i, D2 K (P i) ≤ Z i) ∧
        (∀ s ∈ sd (sd K), ∃ i, s ∈ Z i) ∧
        (∀ i, CategoricalIn (hZ i).1) := by
  have hAK : A ≤ K := by
    rw [hK]
    exact le_sup_left
  have hSK : simplex S ≤ K := by
    rw [hK]
    exact le_sup_right
  have catK (i : Bool) : CategoricalIn ((hPA i).trans hAK) := by
    obtain ⟨c, hc⟩ := hcat i
    exact ⟨includeSubcomplex hAK c, comp_chains id (includeSubcomplex hAK)
      id_simplicial (include_subcomplex_simplicial hAK) hc⟩
  have regions (i : Bool) := mixed_region ((hPA i).trans hAK) hSK haS (hsub i) (ha i)
    (hne i) (hH i) (hmissing i) (hext i) (catK i)
  choose Z hZ hOld hNew hCat using regions
  refine ⟨Z, hZ, hOld, ?_, hCat⟩
  intro s hs
  have hKU : K ≤ A ⊔ simplex S := by rw [hK]
  have hsup := hKU (originalSupport_mem 2 hs)
  rcases (show originalSupport K 2 s ∈ A ∨ originalSupport K 2 s ∈ simplex S from hsup) with h | h
  · rw [← hcover] at h
    rcases h with h | h
    · exact ⟨false, hOld false ((mem_iteratedSubcomplex_iff 2 hs).mpr h)⟩
    · exact ⟨true, hOld true ((mem_iteratedSubcomplex_iff 2 hs).mpr h)⟩
  · have hsσ : s ∈ iteratedSubcomplex K (simplex S) 2 := (mem_iteratedSubcomplex_iff 2 hs).mpr h
    rw [← map_emb hSK 2] at hsσ
    obtain ⟨t, ht, rfl⟩ := hsσ
    change t ∈ sd (sd (simplex S)) at ht
    rw [← mixed_block_cover S a (blocks false) (blocks true) (ha false) (ha true) hdisj] at ht
    rcases ht with ht | ht
    · exact ⟨false, hNew false (image_mem_map _ ht)⟩
    · exact ⟨true, hNew true (image_mem_map _ ht)⟩

/-- At the third ordinary subdivision the full cover gives exactly the
prescribed two old restrictions. -/
theorem mixed_exact_transport [Finite V] (P : Bool → PreAbstractSimplicialComplex V)
    (blocks : Bool → Finset V) (hK : K = A ⊔ simplex S)
    (hcover : P false ⊔ P true = A)
    (hPA : ∀ i, P i ≤ A) (haS : a ∈ S)
    (hsub : ∀ i, blocks i ⊆ S)
    (ha : ∀ i, a ∉ blocks i) (hne : ∀ i, (blocks i).Nonempty)
    (hdisj : Disjoint (blocks false) (blocks true))
    (hH : ∀ i, horn a (blocks i) ≤ P i)
    (hmissing : ∀ i s, s ∈ P i → s ∈ simplex S → ¬ blocks i ⊆ s)
    (hext : ∀ i s, s ∈ P i → s ∉ simplex S → ∀ x ∈ s, x ∈ S → x ∈ insert a (blocks i))
    (hcat : ∀ i, CategoricalIn (hPA i)) :
    ∃ Y : Bool → PreAbstractSimplicialComplex (Face (sd (sd K))),
      ∃ hY : ∀ i, Y i ≤ sd (sd (sd K)),
        (∀ s ∈ sd (sd (sd K)), ∃ i, s ∈ Y i) ∧
        (∀ i, Y i ⊓ iteratedSubcomplex K A 3 = iteratedSubcomplex K (P i) 3) ∧
        ∀ i, CategoricalIn (hY i) := by
  obtain ⟨Z, hZ, hOld, hZcover, hZcat⟩ :=
    mixed_full_cover P blocks hK hcover hPA haS hsub ha hne hdisj hH hmissing hext hcat
  letI : Finite (iteratedAmbient K 2).fst := inferInstanceAs (Finite (Face (sd K)))
  refine exact_extension_of_full_cover (T := D2 K A) (fun i => D2 K (P i)) Z
    (fun i => d2_le K (hPA i)) hOld hZ ?_ hZcover hZcat
  intro s hs
  rw [← hcover, d2_sup] at hs
  rcases (show s ∈ D2 K (P false) ∨ s ∈ D2 K (P true) from hs) with hf | ht
  · exact ⟨false, hf⟩
  · exact ⟨true, ht⟩

end Attachment

end

end D5.S3.Topology.StableCategory.MixedSimplexAttachment
