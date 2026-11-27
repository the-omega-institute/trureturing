/- GID: D5/S3/Topology/CofaceTriangleCollapse
   generality: G
   mirror-B: D5/B/S3/Topology/CofaceTriangleCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Comparable coface labels of size at most three give a contiguous retraction onto a graph. -/

module

public import D5.S3.Topology.BarycentricBaseRigidity
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import OmegaBuild.Commands

/-! A graph retraction for comparable coface labels, as in the selective-boundary
argument for Mosquera-Lois–Tanaka Question 6.3. -/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.Topology.CofaceTriangleCollapse

open BarycentricGraphDistance (Face Vertex)
open BarycentricNeighborhoodIteration (FullIn)
open BarycentricBaseRigidity (Contiguous faceImage includeVertex)

universe u

variable {V : Type u} {G K H : PreAbstractSimplicialComplex V}

noncomputable section

local instance classicalDecEq (X : Type u) : DecidableEq X := Classical.decEq X

private def vertexOfMem {s : Finset V} (hs : s ∈ G) (x : {v // v ∈ s}) : Vertex G :=
  ⟨x.val, (G.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr x.property)
    (Finset.singleton_nonempty x.val)⟩

private theorem mem_faceImage_iff (f : Vertex G → Vertex H) {s : Finset V}
    (hs : s ∈ G) (y : V) : y ∈ faceImage f hs ↔ ∃ x : Vertex G, x.val ∈ s ∧ (f x).val = y := by
  classical
  unfold faceImage
  constructor
  · intro hy
    obtain ⟨x, _, hxy⟩ := Finset.mem_image.mp hy
    exact ⟨vertexOfMem hs x, x.property, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨x.val, hx⟩, Finset.mem_attach _ _, rfl⟩

variable (label : Vertex G → Face K)
variable (hcontains : ∀ x, x.val ∈ (label x).val)
variable (hcmp : ∀ ⦃s : Finset V⦄, s ∈ G → ∀ ⦃x y : Vertex G⦄,
  x.val ∈ s → y.val ∈ s → (label x).val ⊆ (label y).val ∨ (label y).val ⊆ (label x).val)

include hcontains hcmp

private theorem exists_label_contains_face {s : Finset V} (hs : s ∈ G) :
    ∃ z : Vertex G, z.val ∈ s ∧ s ⊆ (label z).val := by
  classical
  -- Comparability turns a label of greatest cardinality into a greatest label.
  let size (x : {v // v ∈ s}) := (label (vertexOfMem hs x)).val.card
  obtain ⟨z, _, hzmax⟩ := Finset.exists_max_image s.attach size
    (Finset.attach_nonempty_iff.mpr (G.isRelLowerSet_faces hs).1)
  refine ⟨vertexOfMem hs z, z.property, ?_⟩
  intro v hv
  let x : {w // w ∈ s} := ⟨v, hv⟩
  have hle : size x ≤ size z := hzmax x (Finset.mem_attach _ _)
  rcases hcmp hs (x := vertexOfMem hs x) (y := vertexOfMem hs z) hv z.property with h | h
  · exact h (hcontains (vertexOfMem hs x))
  · have he := Finset.eq_of_subset_of_card_le h hle
    rw [he]
    exact hcontains (vertexOfMem hs x)

variable (hcard : ∀ x, (label x).val.card ≤ 3)

include hcard

/-- Each triangle has an owner whose label is the triangle. Every source face
through that owner is contained in the triangle. -/
theorem exists_triangle_owner {t : Finset V} (ht : t ∈ G) (htcard : t.card = 3) :
    ∃ z : Vertex G, z.val ∈ t ∧ (label z).val = t ∧
      ∀ ⦃s : Finset V⦄, s ∈ G → z.val ∈ s → s ⊆ t := by
  obtain ⟨z, hz, hsub⟩ := exists_label_contains_face label hcontains hcmp ht
  have he : t = (label z).val := Finset.eq_of_subset_of_card_le hsub
    (by simpa only [htcard] using hcard z)
  refine ⟨z, hz, he.symm, ?_⟩
  intro s hs hzs v hv
  let x := vertexOfMem hs ⟨v, hv⟩
  have h := hcmp hs (x := x) (y := z) hv hzs
  rw [← he] at h
  rcases h with h | h
  · exact h (hcontains x)
  · have hxt : t = (label x).val := Finset.eq_of_subset_of_card_le h
      (by simpa only [htcard] using hcard x)
    rw [hxt]
    exact hcontains x

/-- Comparable coface labels of cardinality at most three give a simplicial
retraction onto a full subcomplex of dimension at most one, contiguous to the
identity after inclusion. A vertex is sent into its own label and is fixed if
its label has cardinality at most two. -/
theorem exists_contiguous_graph_retraction :
    ∃ (H : PreAbstractSimplicialComplex V) (hHG : FullIn H G) (q : Vertex G → Vertex H),
      (∀ s ∈ H, (s : Finset V).card ≤ 2) ∧
      (∀ (s : Finset V) (hs : s ∈ G), faceImage q hs ∈ H) ∧
      (∀ x : Vertex H, q (includeVertex hHG.1 x) = x) ∧
      Contiguous (id : Vertex G → Vertex G) (includeVertex hHG.1 ∘ q) ∧
      ∀ x : Vertex G, (q x).val ∈ (label x).val ∧
        ((label x).val.card ≤ 2 → (q x).val = x.val) := by
  classical
  let Triangle := {t : Finset V // t ∈ G ∧ t.card = 3}
  have howners (t : Triangle) : ∃ z : Vertex G, z.val ∈ t.val ∧ (label z).val = t.val ∧
      ∀ ⦃s : Finset V⦄, s ∈ G → z.val ∈ s → s ⊆ t.val :=
    exists_triangle_owner label hcontains hcmp hcard t.property.1 t.property.2
  let owner (t : Triangle) : Vertex G := (howners t).choose
  have howner_mem (t : Triangle) : (owner t).val ∈ t.val := (howners t).choose_spec.1
  have howner_label (t : Triangle) : (label (owner t)).val = t.val :=
    (howners t).choose_spec.2.1
  have howner_subset (t : Triangle) {s : Finset V} (hs : s ∈ G) (hz : (owner t).val ∈ s) :
      s ⊆ t.val := (howners t).choose_spec.2.2 hs hz
  have howner_unique (t u : Triangle) (hu : (owner u).val ∈ t.val) : t = u :=
    Subtype.ext (Finset.eq_of_subset_of_card_le (howner_subset u t.property.1 hu)
      (u.property.2.trans t.property.2.symm).le)
  let moved (v : V) : Prop := ∃ t : Triangle, (owner t).val = v
  have hpartners (t : Triangle) : ∃ b ∈ t.val, b ≠ (owner t).val := by
    apply Finset.exists_mem_ne _ (owner t).val
    rw [t.property.2]
    decide
  let partner (t : Triangle) : V := (hpartners t).choose
  have hpartner_mem (t : Triangle) : partner t ∈ t.val := (hpartners t).choose_spec.1
  have hpartner_retained (t : Triangle) : ¬ moved (partner t) := by
    rintro ⟨u, hu⟩
    have hut : (owner u).val ∈ t.val := by
      rw [hu]
      exact hpartner_mem t
    have he := howner_unique t u hut
    subst u
    exact (hpartners t).choose_spec.2 hu.symm
  let H : PreAbstractSimplicialComplex V :=
    { faces := {s | s ∈ G ∧ ∀ v ∈ s, ¬ moved v}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨(G.isRelLowerSet_faces hs.1).1, ?_⟩
        intro t hts ht
        exact ⟨(G.isRelLowerSet_faces hs.1).2 hts ht, fun v hv => hs.2 v (hts hv)⟩ }
  have hHG : FullIn H G :=
    ⟨fun _ hs => hs.1, fun s hs =>
      ⟨s.property, fun v hv => (hs v hv).2 v (Finset.mem_singleton_self v)⟩⟩
  let value (x : Vertex G) : V := if hx : moved x.val then partner hx.choose else x.val
  have hvalue (x : Vertex G) (hx : moved x.val) : value x = partner hx.choose := dif_pos hx
  have hfix (x : Vertex G) (hx : ¬ moved x.val) : value x = x.val := dif_neg hx
  have hretained (x : Vertex G) : ¬ moved (value x) := by
    by_cases hx : moved x.val
    · rw [hvalue x hx]
      exact hpartner_retained hx.choose
    · rwa [hfix x hx]
  have hvertex (x : Vertex G) : ({value x} : Finset V) ∈ G := by
    by_cases hx : moved x.val
    · rw [hvalue x hx]
      exact (vertexOfMem hx.choose.property.1 ⟨partner hx.choose, hpartner_mem hx.choose⟩).property
    · rw [hfix x hx]
      exact x.property
  let q (x : Vertex G) : Vertex H :=
    ⟨value x, hvertex x, fun v hv => by
      rw [Finset.mem_singleton.mp hv]
      exact hretained x⟩
  have hunion (s : Finset V) (hs : s ∈ G) : s ∪ faceImage q hs ∈ G := by
    have hne : (s ∪ faceImage q hs).Nonempty :=
      (G.isRelLowerSet_faces hs).1.mono Finset.subset_union_left
    have union_subset {t : Finset V} (hsub : s ⊆ t)
        (hm : ∀ x : Vertex G, x.val ∈ s → moved x.val → value x ∈ t) :
        s ∪ faceImage q hs ⊆ t := by
      apply Finset.union_subset hsub
      intro y hy
      obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff q hs y).mp hy
      change value x ∈ t
      by_cases hx' : moved x.val
      · exact hm x hx hx'
      · rw [hfix x hx']
        exact hsub hx
    by_cases h : ∃ x : Vertex G, x.val ∈ s ∧ moved x.val
    · obtain ⟨x, hx, hm⟩ := h
      -- The face and every replacement lie in the triangle of this owner.
      let t : Triangle := hm.choose
      have hown : (owner t).val ∈ s := by
        change (owner hm.choose).val ∈ s
        rwa [hm.choose_spec]
      have hsub := howner_subset t hs hown
      refine (G.isRelLowerSet_faces t.property.1).2 (union_subset hsub ?_) hne
      intro y hy hy'
      have hyt : (owner hy'.choose).val ∈ t.val := by
        rw [hy'.choose_spec]
        exact hsub hy
      have he := howner_unique t hy'.choose hyt
      rw [hvalue y hy', ← he]
      exact hpartner_mem t
    · exact (G.isRelLowerSet_faces hs).2
        (union_subset (Finset.Subset.refl _) (fun x hx hm => (h ⟨x, hx, hm⟩).elim)) hne
  refine ⟨H, hHG, q, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨z, _, hz⟩ := exists_label_contains_face label hcontains hcmp hs.1
    have hsle := (Finset.card_le_card hz).trans (hcard z)
    by_contra h
    have hs3 : s.card = 3 := by omega
    let t : Triangle := ⟨s, hs.1, hs3⟩
    exact hs.2 (owner t).val (howner_mem t) ⟨t, rfl⟩
  · intro s hs
    have hne : (faceImage q hs).Nonempty := by
      unfold faceImage
      exact Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr
        (G.isRelLowerSet_faces hs).1)
    refine ⟨(G.isRelLowerSet_faces (hunion s hs)).2 Finset.subset_union_right hne, ?_⟩
    intro y hy
    obtain ⟨x, _, rfl⟩ := (mem_faceImage_iff q hs y).mp hy
    exact hretained x
  · intro x
    apply Subtype.ext
    exact hfix (includeVertex hHG.1 x) (x.property.2 x.val (Finset.mem_singleton_self _))
  · intro s hs
    have hid : faceImage (id : Vertex G → Vertex G) hs = s := by
      ext y
      rw [mem_faceImage_iff]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact (show x.val = y from hxy) ▸ hx
      · intro hy
        exact ⟨vertexOfMem hs ⟨y, hy⟩, hy, rfl⟩
    change faceImage (id : Vertex G → Vertex G) hs ∪ faceImage q hs ∈ G
    rw [hid]
    exact hunion s hs
  · intro x
    change value x ∈ (label x).val ∧ ((label x).val.card ≤ 2 → value x = x.val)
    by_cases hx : moved x.val
    · have he : owner hx.choose = x := Subtype.ext hx.choose_spec
      have hl : (label x).val = hx.choose.val :=
        (congrArg (fun z => (label z).val) he.symm).trans (howner_label hx.choose)
      rw [hvalue x hx, hl]
      exact ⟨hpartner_mem hx.choose, fun hc => by
        have hc3 := hx.choose.property.2
        omega⟩
    · rw [hfix x hx]
      exact ⟨hcontains x, fun _ => rfl⟩

end

end D5.S3.Topology.CofaceTriangleCollapse
