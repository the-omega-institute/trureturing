/- GID: D5/S3/Topology/SubdivisionCategoricalCover
   generality: G
   mirror-B: D5/B/S3/Topology/SubdivisionCategoricalCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.NonemptyFiniteChains]
   utility: none
   digest: Categorical vertex covers yield lower covers after two subdivisions. -/

module

public import D5.S3.Topology.ConnectedCategoryGraft
public import Mathlib.Order.NonemptyFiniteChains
import D5.S3.Topology.DescendingClosureContiguity
import Mathlib.Data.Fintype.Powerset
import OmegaBuild.Commands

/-!
# Categorical covers after two ordinary subdivisions

This transfer theorem for Conjecture 6.1 of Mosquera-Lois and Tanaka converts a
two-piece categorical cover of a finite poset to a categorical lower cover
after two ordinary subdivisions. See https://arxiv.org/abs/2609.39615v1.
Each piece consists of flags whose every face meets the corresponding vertex set.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.SubdivisionCategoricalCover

open ConnectedCategoryGraft DescendingClosureContiguity
open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)

variable {P Q : Type*} [PartialOrder P] [PartialOrder Q]

private theorem isChain_finset (s : NonemptyFiniteChains P) :
    IsChain (· ≤ ·) (s.finset : Set P) :=
  fun x hx y hy _ => s.comparable ⟨x, hx⟩ ⟨y, hy⟩

open scoped Classical in
private def unionMap (f g : P →o Q)
    (h : ∀ s : Set P, IsChain (· ≤ ·) s → IsChain (· ≤ ·) (f '' s ∪ g '' s)) :
    NonemptyFiniteChains P →o NonemptyFiniteChains Q where
  toFun s := {
    finset := (s.map f).finset ∪ (s.map g).finset
    nonempty := (s.map f).nonempty.mono Finset.subset_union_left
    comparable := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      change x ≤ y ∨ y ≤ x
      by_cases he : x = y
      · exact Or.inl he.le
      · have hc : IsChain (· ≤ ·)
            (↑((s.map f).finset ∪ (s.map g).finset) : Set Q) := by
          simpa only [NonemptyFiniteChains.map, Finset.coe_union, Finset.coe_image] using
            h (s.finset : Set P) (isChain_finset s)
        exact hc hx hy he }
  monotone' _ _ hab := Finset.union_subset_union
    ((orderHomMap f).monotone hab) ((orderHomMap g).monotone hab)

private theorem orderHomMap_fence_of_le [Finite P] {f g : P →o Q} (hfg : f ≤ g) :
    Relation.EqvGen (· ≤ ·) (orderHomMap f) (orderHomMap g) := by
  classical
  let := Fintype.ofFinite P
  let lower (x : P) : Finset P := Finset.univ.filter (· ≤ x)
  let rank (x : P) : ℕ := (lower x).card
  have hmem (x z : P) : z ∈ lower x ↔ z ≤ x := by simp [lower]
  have hstrict : StrictMono rank := by
    intro x y hxy
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      exact (hmem y z).mpr (((hmem x z).mp hz).trans hxy.le)
    · intro he
      have hy : y ∈ lower y := (hmem y y).mpr le_rfl
      have hy' : y ∈ lower x := he.symm ▸ hy
      exact (not_le_of_gt hxy) ((hmem x y).mp hy')
  have hbound (x : P) : rank x ≤ Fintype.card P := Finset.card_le_univ _
  obtain ⟨F, hzero, hlast, _, _, hstep⟩ :=
    exists_relative_contiguity_of_le rank hstrict g f (OrderHom.le_def.mp hfg) _ hbound
  have path (k : ℕ) :
      Relation.EqvGen (· ≤ ·) (orderHomMap (F 0)) (orderHomMap (F k)) := by
    induction k with
    | zero => exact .refl _
    | succ k ih =>
      let top := unionMap (F k) (F (k + 1)) (hstep k)
      have hleft : orderHomMap (F k) ≤ top := fun _ => Finset.subset_union_left
      have hright : orderHomMap (F (k + 1)) ≤ top := fun _ => Finset.subset_union_right
      exact .trans _ _ _ ih (.trans _ _ _ (.rel _ _ hleft) (.symm _ _ (.rel _ _ hright)))
  have hgf : Relation.EqvGen (· ≤ ·) (orderHomMap g) (orderHomMap f) := by
    simpa only [hzero, hlast] using path (Fintype.card P + 1)
  exact .symm _ _ hgf

private theorem map_fence {X Y : Type*} [LE X] [LE Y] (m : X → Y)
    (hm : ∀ x y, x ≤ y → Relation.EqvGen (· ≤ ·) (m x) (m y)) {x y : X}
    (h : Relation.EqvGen (· ≤ ·) x y) : Relation.EqvGen (· ≤ ·) (m x) (m y) := by
  induction h with
  | rel a b hab => exact hm a b hab
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Subdivision sends a finite fence of order maps out of a finite poset to a
finite fence of their induced maps on nonempty chains. -/
theorem subdivision_map_fence [Finite P] {f g : P →o Q} (h : Relation.EqvGen (· ≤ ·) f g) :
    Relation.EqvGen (· ≤ ·) (orderHomMap f) (orderHomMap g) :=
  map_fence orderHomMap (fun _ _ hle => orderHomMap_fence_of_le hle) h

open scoped Classical in
private def singletonChain (x : P) : NonemptyFiniteChains P where
  finset := {x}
  nonempty := Finset.singleton_nonempty x
  comparable := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    change a ≤ b ∨ b ≤ a
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact Or.inl le_rfl

private theorem orderHomMap_const (q : Q) :
    orderHomMap (OrderHom.const P q) =
      OrderHom.const (NonemptyFiniteChains P) (singletonChain q) := by
  classical
  apply OrderHom.ext
  funext s
  apply NonemptyFiniteChains.ext
  change (s.finset.image fun _ => q) = {q}
  exact Finset.image_const s.nonempty q

open scoped Classical in
/-- Intersect the chain with `U` and view the remaining vertices in the subtype. -/
private def restrictChains (U : Set P) {V : Set (NonemptyFiniteChains P)}
    (hmeet : ∀ s : V, ∃ x ∈ s.val.finset, x ∈ U) : V →o NonemptyFiniteChains U where
  toFun s := {
    finset := s.val.finset.subtype (· ∈ U)
    nonempty := by
      obtain ⟨x, hx, hU⟩ := hmeet s
      exact ⟨⟨x, hU⟩, Finset.mem_subtype.mpr hx⟩
    comparable := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      exact s.val.comparable ⟨x.val, Finset.mem_subtype.mp hx⟩
        ⟨y.val, Finset.mem_subtype.mp hy⟩ }
  monotone' _ _ hab := Finset.subtype_mono hab

private theorem categorical_of_meeting [Finite P] {U : Set P}
    {V : Set (NonemptyFiniteChains P)} (hU : Categorical U)
    (hmeet : ∀ s : V, ∃ x ∈ s.val.finset, x ∈ U) : Categorical V := by
  classical
  let r := restrictChains U hmeet
  let incl : U →o P := (OrderEmbedding.subtype U).toOrderHom
  have hstart : (orderHomMap incl).comp r ≤ (OrderEmbedding.subtype V).toOrderHom := by
    intro s x hx
    change x ∈ ((r s).map incl).finset at hx
    obtain ⟨y, hy, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hx
    exact Finset.mem_subtype.mp hy
  obtain ⟨c, hc⟩ := hU
  have hfence : Relation.EqvGen (· ≤ ·) ((orderHomMap incl).comp r)
      ((orderHomMap (OrderHom.const U c)).comp r) :=
    map_fence (fun f : NonemptyFiniteChains U →o NonemptyFiniteChains P => f.comp r)
      (fun _ _ hab => .rel _ _ (fun s => (OrderHom.le_def.mp hab) (r s))) (subdivision_map_fence hc)
  rw [orderHomMap_const, OrderHom.const_comp] at hfence
  exact ⟨singletonChain c, .trans _ _ _ (.symm _ _ (.rel _ _ hstart)) hfence⟩

private def chainComplex (P : Type*) [PartialOrder P] : PreAbstractSimplicialComplex P where
  faces := {s | s.Nonempty ∧ IsChain (· ≤ ·) (s : Set P)}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun _ hts ht => ⟨ht, hs.2.mono (Finset.coe_subset.mpr hts)⟩⟩

private def toFace : NonemptyFiniteChains P →o Faces (chainComplex P) :=
  ⟨fun s => ⟨s.finset, s.nonempty, isChain_finset s⟩, fun _ _ h => h⟩

open scoped Classical in
/-- The predicate of `MeetingFace` on Mathlib's nonempty-chain poset. -/
private def meetingFaces (S : Finset P) : Set (NonemptyFiniteChains P) :=
  {s | (s.finset ∩ S).Nonempty}

private def flagsMeeting (S : Finset P) : Set (NonemptyFiniteChains (NonemptyFiniteChains P)) :=
  {s | ∀ f ∈ s.finset, f ∈ meetingFaces S}

private theorem categorical_flagsMeeting [Finite P] (S : Finset P)
    (hS : Categorical (S : Set P)) : Categorical (flagsMeeting S) := by
  classical
  have hface : Categorical (meetingFaces S) := by
    apply categorical_of_meeting hS
    intro s
    have hs : (s.val.finset ∩ S).Nonempty := s.property
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
  let : Finite (NonemptyFiniteChains P) := by
    let := Fintype.ofFinite P
    exact Finite.of_injective (fun s : NonemptyFiniteChains P => s.finset)
      (fun _ _ h => NonemptyFiniteChains.ext h)
  apply categorical_of_meeting hface
  intro s
  obtain ⟨f, hf⟩ := s.val.nonempty
  exact ⟨f, hf, s.property f hf⟩

private theorem flagsMeeting_lower (S : Finset P) : IsLowerSet (flagsMeeting S) :=
  fun _ _ hab hb f hf => hb f (hab hf)

private theorem flagsMeeting_cover (A B : Finset P) (hcover : ∀ x : P, x ∈ A ∨ x ∈ B)
    (s : NonemptyFiniteChains (NonemptyFiniteChains P)) :
    s ∈ flagsMeeting A ∨ s ∈ flagsMeeting B := by
  classical
  let C : Set (Faces (chainComplex P)) := toFace '' (s.finset : Set (NonemptyFiniteChains P))
  have hC : IsChain (· ≤ ·) C :=
    IsChain.image_of_map_rel (· ≤ ·) (· ≤ ·) toFace
      (fun _ _ h => toFace.monotone h) (isChain_finset s)
  rcases two_subsets_cover_face_flags (chainComplex P) A B hcover C hC with hA | hB
  · exact Or.inl fun f hf => hA (toFace f) ⟨f, hf, rfl⟩
  · exact Or.inr fun f hf => hB (toFace f) ⟨f, hf, rfl⟩

/-- A cover of a finite poset by two categorical subposets gives a categorical
lower cover of its second ordinary subdivision by two pieces. -/
theorem hasCategoricalCover_double_subdivision [Finite P] {A B : Set P}
    (hA : Categorical A) (hB : Categorical B) (hcover : ∀ x : P, x ∈ A ∨ x ∈ B) :
    HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains P)) 2 := by
  classical
  let := Fintype.ofFinite P
  let SA : Finset P := Finset.univ.filter (· ∈ A)
  let SB : Finset P := Finset.univ.filter (· ∈ B)
  have hSA : (SA : Set P) = A := by
    ext x
    change x ∈ SA ↔ x ∈ A
    simp [SA]
  have hSB : (SB : Set P) = B := by
    ext x
    change x ∈ SB ↔ x ∈ B
    simp [SB]
  have hvertices (x : P) : x ∈ SA ∨ x ∈ SB := by
    change x ∈ (SA : Set P) ∨ x ∈ (SB : Set P)
    rw [hSA, hSB]
    exact hcover x
  let U (i : Fin 2) := if i = 0 then flagsMeeting SA else flagsMeeting SB
  refine ⟨U, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · simpa only [U, ite_eq_left hi] using
        And.intro (flagsMeeting_lower SA) (categorical_flagsMeeting SA (hSA.symm ▸ hA))
    · simpa only [U, ite_eq_right hi] using
        And.intro (flagsMeeting_lower SB) (categorical_flagsMeeting SB (hSB.symm ▸ hB))
  · intro s
    rcases flagsMeeting_cover SA SB hvertices s with hs | hs
    · exact ⟨0, by simpa only [U, ite_eq_left (rfl : (0 : Fin 2) = 0)] using hs⟩
    · have hne : (1 : Fin 2) ≠ 0 := by decide
      exact ⟨1, by simpa only [U, ite_eq_right hne] using hs⟩

end D5.S3.Topology.SubdivisionCategoricalCover

end
