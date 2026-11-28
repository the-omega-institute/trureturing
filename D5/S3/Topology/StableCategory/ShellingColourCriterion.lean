/- GID: D5/S3/Topology/StableCategory/ShellingColourCriterion
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/ShellingColourCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed shelling restriction faces give a categorical two-cover. -/

import D5.S3.Topology.StableCategory.ExactCategoricalExtension
import D5.S3.Topology.StableCategory.InducedCategoricalCover

/-!
# The two-colour restriction-face criterion

A shelling with mixed nonsingleton restriction faces and connected final
one-skeleton yields a two-set categorical lower cover after one subdivision of
the face poset. This is a sufficient
criterion toward Question 6.3 of https://arxiv.org/html/2609.39615v1#S6.

We use `FiniteAlexanderDualCollapse.simplex` for the starting complex, the
induced subcomplexes from `OrdinaryCollarRetraction`, the contiguity and
composition API from `OrdinaryContiguityLift`, and the transfer
`InducedCategoricalCover.has_categorical_cover_of_partition`. The isolated
vertex case extends the old chain with that vertex fixed, then moves it along
the ambient one-skeleton, as in the disjoint gluing argument of
`DisjointContiguityGluing`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.ShellingColourCriterion

open BarycentricBaseRigidity (Contiguous faceImage skeleton)
open BarycentricGraphDistance (Face Vertex)
open ConnectedCategoryGraft (HasCategoricalCover)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open ExactCategoricalExtension (CategoricalIn)
open GraphSubdivisionIntervals (faceImage_singleton)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (includeSubcomplex include_subcomplex_simplicial
  comp_chains constant_chain_of_reachable ofTotal of_total_simplicial)
open PartialOrder (NonemptyFiniteChains)
open Relation (ReflTransGen)

open private constant_face_image ofTotal_faceImage from
  D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private face_image_comp face_image_include id_simplicial from
  D5.S3.Topology.StableCategory.FourPieceCategoricalCover
open private image from D5.S3.Topology.OrdinarySubdivisionMap

noncomputable section

local instance (priority := 2000) (V : Type*) : DecidableEq V := Classical.decEq V
attribute [local instance] Classical.propDecidable

variable {V : Type} {A P Q K : PreAbstractSimplicialComplex V}

private abbrev ContractsAt (h : P ≤ K) (b : Vertex K) : Prop :=
  ReflTransGen Contiguous (includeSubcomplex h) (fun _ => b)

private theorem colour_le (J : PreAbstractSimplicialComplex V) (p : V → Bool) :
    colourComplex J p ≤ J := fun _ hs => hs.1

private theorem colour_mono (h : P ≤ Q) (p : V → Bool) :
    colourComplex P p ≤ colourComplex Q p := fun _ hs => ⟨h hs.1, hs.2⟩

private theorem singleton_mem {s : Finset V} (hs : s ∈ P) {x : V} (hx : x ∈ s) :
    ({x} : Finset V) ∈ P :=
  (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)

private theorem restrict_contract (hAK : A ≤ K) (hPK : P ≤ K) (hPA : P ≤ A)
    {b : Vertex K} (h : ContractsAt hAK b) : ContractsAt hPK b :=
  comp_chains (includeSubcomplex hPA) id
    (include_subcomplex_simplicial hPA) id_simplicial h

private theorem contract_simplex (p : V → Bool) (hPK : P ≤ K)
    (b : Vertex K) (connected : ∀ a : Vertex K, (skeleton K).Reachable a b)
    {F : Finset V} (faces : ∀ s, s ∈ P ↔ s.Nonempty ∧ s ⊆ F) :
    ContractsAt ((colour_le P p).trans hPK) b := by
  let h : colourComplex P p ≤ K := (colour_le P p).trans hPK
  by_cases hF : F.Nonempty
  · obtain ⟨a, ha⟩ := hF
    let aK : Vertex K := ⟨a, hPK ((faces _).mpr
      ⟨Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩)⟩
    have step : Contiguous (includeSubcomplex h) (fun _ => aK) := by
      intro s hs
      rw [face_image_include, constant_face_image]
      obtain ⟨hne, hsub⟩ := (faces s).mp hs.1
      exact hPK ((faces _).mpr ⟨hne.mono Finset.subset_union_left,
        Finset.union_subset hsub (Finset.singleton_subset_iff.mpr ha)⟩)
    exact (ReflTransGen.single step).trans (constant_chain_of_reachable (connected aK))
  · have same : includeSubcomplex h = (fun _ : Vertex (colourComplex P p) => b) := by
      funext x
      exact (hF ((Finset.singleton_nonempty x.val).mono ((faces _).mp x.property.1).2)).elim
    change ReflTransGen Contiguous (includeSubcomplex h) (fun _ => b)
    rw [same]

private theorem contract_with_isolated_vertex
    (hAK : A ≤ K) (hPK : P ≤ K) (hAP : A ≤ P) (a b : Vertex K)
    (ha : ({a.val} : Finset V) ∉ A)
    (isolated : ∀ s ∈ P, s ∉ A → s = {a.val})
    (reachable : (skeleton K).Reachable a b)
    (previous : ContractsAt hAK b) : ContractsAt hPK b := by
  let extend (f : Vertex A → Vertex K) (c : Vertex K) (x : Vertex P) : Vertex K :=
    if hx : ({x.val} : Finset V) ∈ A then f ⟨x.val, hx⟩ else c
  have oldImage (f : Vertex A → Vertex K) (c : Vertex K)
      {s : Finset V} (hs : s ∈ A) :
      faceImage (extend f c) (hAP hs) = faceImage f hs := by
    unfold faceImage
    apply Finset.image_congr
    intro x _
    simp only [extend, dite_eq_left (singleton_mem hs x.property)]
  have glueStep {f g : Vertex A → Vertex K} {c d : Vertex K}
      (oldStep : Contiguous f g) (edge : ({c.val, d.val} : Finset V) ∈ K) :
      Contiguous (extend f c) (extend g d) := by
    intro s hs
    by_cases hsA : s ∈ A
    · rw [oldImage f c hsA, oldImage g d hsA]
      exact oldStep s hsA
    · obtain rfl := isolated s hs hsA
      let x : Vertex P := ⟨a.val, hs⟩
      rw [faceImage_singleton (extend f c) x, faceImage_singleton (extend g d) x]
      have at_isolated (e : Vertex A → Vertex K) (z : Vertex K) : extend e z x = z := by
        change (if hx : ({a.val} : Finset V) ∈ A then e ⟨a.val, hx⟩ else z) = z
        rw [dite_eq_right ha]
      rw [at_isolated f c, at_isolated g d, Finset.singleton_union]
      exact edge
  have start : extend (includeSubcomplex hAK) a = includeSubcomplex hPK := by
    funext x
    by_cases hx : ({x.val} : Finset V) ∈ A
    · simp only [extend, dite_eq_left hx, includeSubcomplex]
    · apply Subtype.ext
      simpa only [extend, dite_eq_right hx, includeSubcomplex] using
        (Finset.singleton_inj.mp (isolated _ x.property hx)).symm
  have finish : extend (fun _ => b) b = (fun _ => b) := by
    funext x
    by_cases hx : ({x.val} : Finset V) ∈ A <;> simp [extend, hx]
  have fixed : ({a.val, a.val} : Finset V) ∈ K := by
    simpa only [Finset.pair_eq_singleton] using a.property
  have oldChain : ReflTransGen Contiguous
      (extend (includeSubcomplex hAK) a) (extend (fun _ => b) a) := by
    refine ReflTransGen.lift (fun f => extend f a) ?_ _ _ previous
    intro f g h
    exact glueStep h fixed
  have constStep : Contiguous (fun _ : Vertex A => b) (fun _ => b) := by
    intro s hs
    rw [constant_face_image, Finset.union_idempotent]
    exact b.property
  have walk : ReflTransGen (skeleton K).Adj a b :=
    (SimpleGraph.reachable_iff_reflTransGen (G := skeleton K) a b).mp reachable
  have newChain : ReflTransGen Contiguous
      (extend (fun _ => b) a) (extend (fun _ => b) b) := by
    refine ReflTransGen.lift (extend (fun _ => b)) ?_ _ _ walk
    intro c d h
    exact glueStep constStep h.2
  simpa only [start, finish] using oldChain.trans newChain

private theorem contract_singleton_attachment (p : V → Bool) (hPQ : P ≤ Q) (hQK : Q ≤ K)
    (b : Vertex K) (connected : ∀ a : Vertex K, (skeleton K).Reachable a b)
    {F : Finset V} {v : V} (hF : F ∈ Q) (hvF : ({v} : Finset V) ⊆ F)
    (new_faces : ∀ s, s ∈ Q ∧ s ∉ P ↔ s.Nonempty ∧ ({v} : Finset V) ⊆ s ∧ s ⊆ F)
    (previous : ContractsAt ((colour_le P p).trans (hPQ.trans hQK)) b) :
    ContractsAt ((colour_le Q p).trans hQK) b := by
  let hOld : colourComplex P p ≤ K := (colour_le P p).trans (hPQ.trans hQK)
  let hNext : colourComplex Q p ≤ K := (colour_le Q p).trans hQK
  have hv := (new_faces {v}).mpr ⟨Finset.singleton_nonempty v, fun _ hx => hx, hvF⟩
  by_cases hw : ∃ w, w ≠ v ∧ w ∈ F ∧ p w = true
  · obtain ⟨w, hwv, hwF, hwp⟩ := hw
    let replace (x : V) : V := if x = v then w else x
    have image_old {s : Finset V} (hs : s ∈ P) : image s replace = s := by
      calc
        _ = image s id := by
          apply Finset.image_congr
          intro x hx
          have hxv : x ≠ v := by
            rintro rfl
            exact hv.2 (singleton_mem hs hx)
          simp only [replace, ite_eq_right hxv, id_eq]
        _ = s := Finset.image_id
    have image_new {s : Finset V} (hs : s ∈ colourComplex Q p) (hsub : s ⊆ F) :
        ∀ y ∈ image s replace, y ∈ F ∧ y ≠ v ∧ p y = true := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      by_cases hxv : x = v
      · simpa only [replace, ite_eq_left hxv] using
          (show w ∈ F ∧ w ≠ v ∧ p w = true from ⟨hwF, hwv, hwp⟩)
      · simpa only [replace, ite_eq_right hxv] using
          (show x ∈ F ∧ x ≠ v ∧ p x = true from ⟨hsub hx, hxv, hs.2 x hx⟩)
    have lands (s : Finset V) (hs : s ∈ colourComplex Q p) :
        image s replace ∈ colourComplex P p := by
      by_cases hsP : s ∈ P
      · rw [image_old hsP]
        exact ⟨hsP, hs.2⟩
      · have hsub := ((new_faces s).mp ⟨hs.1, hsP⟩).2.2
        have inF : image s replace ⊆ F := fun _ hy => (image_new hs hsub _ hy).1
        have inQ : image s replace ∈ Q :=
          (Q.isRelLowerSet_faces hF).2 inF ((Q.isRelLowerSet_faces hs.1).1.image _)
        refine ⟨?_, fun y hy => (image_new hs hsub y hy).2.2⟩
        by_contra hn
        have contains := ((new_faces _).mp ⟨inQ, hn⟩).2.1
        exact (image_new hs hsub v (contains (Finset.mem_singleton_self v))).2.1 rfl
    let r := ofTotal replace lands
    have rSimplicial := of_total_simplicial replace lands
    have ontoOld : Contiguous (includeSubcomplex hNext) (includeSubcomplex hOld ∘ r) := by
      intro s hs
      rw [face_image_include hNext, face_image_comp r (includeSubcomplex hOld) s hs
        (rSimplicial s hs), face_image_include hOld]
      change s ∪ faceImage (ofTotal replace lands) hs ∈ K
      rw [ofTotal_faceImage]
      by_cases hsP : s ∈ P
      · rw [image_old hsP, Finset.union_idempotent]
        exact hQK hs.1
      · have hsub := ((new_faces s).mp ⟨hs.1, hsP⟩).2.2
        exact hQK ((Q.isRelLowerSet_faces hF).2
          (Finset.union_subset hsub (fun _ hy => (image_new hs hsub _ hy).1))
          ((Q.isRelLowerSet_faces hs.1).1.mono Finset.subset_union_left))
    exact (ReflTransGen.single ontoOld).trans (comp_chains r id rSimplicial id_simplicial previous)
  · let a : Vertex K := ⟨v, hQK hv.1⟩
    refine contract_with_isolated_vertex hOld hNext (colour_mono hPQ p) a b
      (fun h => hv.2 h.1) ?_ (connected a) previous
    intro s hs hsOld
    have hn : s ∉ P := fun hsP => hsOld ⟨hsP, hs.2⟩
    have hnew := (new_faces s).mp ⟨hs.1, hn⟩
    refine Finset.Subset.antisymm (fun x hx => Finset.mem_singleton.mpr ?_) hnew.2.1
    by_contra hxv
    exact hw ⟨x, hxv, hnew.2.2 hx, hs.2 x hx⟩

private theorem contract_attachment (p : V → Bool) (hPQ : P ≤ Q) (hQK : Q ≤ K)
    (b : Vertex K) (connected : ∀ a : Vertex K, (skeleton K).Reachable a b)
    {F R : Finset V} (hF : F ∈ Q) (hRF : R ⊆ F)
    (hR : R.Nonempty ∨ P = ⊥)
    (new_faces : ∀ s, s ∈ Q ∧ s ∉ P ↔ s.Nonempty ∧ R ⊆ s ∧ s ⊆ F)
    (small : (∀ x ∈ R, p x = true) → R.card ≤ 1)
    (previous : ContractsAt ((colour_le P p).trans (hPQ.trans hQK)) b) :
    ContractsAt ((colour_le Q p).trans hQK) b := by
  by_cases hP : P = ⊥
  · apply contract_simplex p hQK b connected (F := F)
    intro s
    constructor
    · intro hs
      have hn : s ∉ P := by
        intro hsP
        rw [hP] at hsP
        exact hsP
      have hi := (new_faces s).mp ⟨hs, hn⟩
      exact ⟨hi.1, hi.2.2⟩
    · rintro ⟨hne, hsub⟩
      exact (Q.isRelLowerSet_faces hF).2 hsub hne
  · by_cases hcard : R.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      exact contract_singleton_attachment p hPQ hQK b connected hF hRF new_faces previous
    · have unchanged : colourComplex Q p ≤ colourComplex P p := by
        intro s hs
        refine ⟨?_, hs.2⟩
        by_contra hn
        have hr := ((new_faces s).mp ⟨hs.1, hn⟩).2.1
        exact hcard (Nat.le_antisymm (small (fun x hx => hs.2 x (hr hx)))
          (Finset.card_pos.mpr (hR.resolve_right hP)))
      exact restrict_contract _ _ unchanged previous

/-- Suppose the final one-skeleton is connected and every restriction face of
cardinality at least two is mixed under a fixed binary vertex colouring. Each
induced colour subcomplex contracts in the final ambient complex. The face poset admits a categorical lower cover of size two
after one subdivision. The initial simplex may be empty, and an attachment
with empty restriction is allowed when its preceding prefix is empty. -/
theorem has_categorical_cover_of_mixed_restrictions [Finite V]
    {n : ℕ} (prefixes : ℕ → PreAbstractSimplicialComplex V) (grows : Monotone prefixes)
    (initial : Finset V) (initial_eq : prefixes 0 = simplex initial)
    (facet restriction : ℕ → Finset V) (label : V → Fin 2)
    (facet_mem : ∀ j < n, facet j ∈ prefixes (j + 1))
    (restriction_subset : ∀ j < n, restriction j ⊆ facet j)
    (restriction_nonempty : ∀ j < n, (restriction j).Nonempty ∨ prefixes j = ⊥)
    (new_faces : ∀ j < n, ∀ s, s ∈ prefixes (j + 1) ∧ s ∉ prefixes j ↔
      s.Nonempty ∧ restriction j ⊆ s ∧ s ⊆ facet j)
    (mixed : ∀ j < n, 2 ≤ (restriction j).card →
      ∃ x ∈ restriction j, ∃ y ∈ restriction j, label x ≠ label y)
    (b : Vertex (prefixes n)) (connected : ∀ a : Vertex (prefixes n),
      (skeleton (prefixes n)).Reachable a b) :
    (∀ i : Fin 2, CategoricalIn
      (show colourComplex (prefixes n) (fun x => decide (label x = i)) ≤ prefixes n from
        fun _ hs => hs.1)) ∧
    HasCategoricalCover (NonemptyFiniteChains (Face (prefixes n))) 2 := by
  have initial_faces (s : Finset V) : s ∈ prefixes 0 ↔ s.Nonempty ∧ s ⊆ initial := by
    rw [initial_eq] <;> rfl
  have contract (i : Fin 2) :
      CategoricalIn (colour_le (prefixes n) (fun x => decide (label x = i))) := by
    let p (x : V) : Bool := decide (label x = i)
    have chain (j : ℕ) (hj : j ≤ n) :
        ContractsAt ((colour_le (prefixes j) p).trans (grows hj)) b := by
      induction j with
      | zero => exact contract_simplex p (grows hj) b connected initial_faces
      | succ j ih =>
        have hlt : j < n := hj
        apply contract_attachment p (grows (Nat.le_succ j)) (grows hj) b connected
          (facet_mem j hlt) (restriction_subset j hlt) (restriction_nonempty j hlt) (new_faces j hlt)
        · intro mono
          by_contra hcard
          obtain ⟨x, hx, y, hy, hxy⟩ := mixed j hlt (Nat.succ_le_of_lt (lt_of_not_ge hcard))
          have hx' : label x = i := of_decide_eq_true (mono x hx)
          have hy' : label y = i := of_decide_eq_true (mono y hy)
          exact hxy (hx'.trans hy'.symm)
        · exact ih (Nat.le_of_lt hlt)
    exact ⟨b, chain n le_rfl⟩
  exact ⟨contract, InducedCategoricalCover.has_categorical_cover_of_partition label contract⟩

end

end D5.S3.Topology.StableCategory.ShellingColourCriterion
