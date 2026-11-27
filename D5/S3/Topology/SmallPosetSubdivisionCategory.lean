/- GID: D5/S3/Topology/SmallPosetSubdivisionCategory
   generality: G
   mirror-B: D5/B/S3/Topology/SmallPosetSubdivisionCategory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Preorder.Finite]
   utility: none
   digest: Extremal vertices give stable two-covers in small finite spaces. -/

module

public import D5.S3.Topology.SubdivisionCategoricalCover
public import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic
import OmegaBuild.Commands

/-! Categorical two-covers for finite posets with few intermediate vertices. -/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Topology.SmallPosetSubdivisionCategory

open D5.S3.Topology.ConnectedCategoryGraft
open D5.S3.Topology.SubdivisionCategoricalCover

variable {X : Type*} [PartialOrder X]

private theorem mapFence {A B : Type*} [LE A] [LE B] (F : A → B)
    (hF : ∀ a b, a ≤ b → Relation.EqvGen (· ≤ ·) (F a) (F b)) {a b : A}
    (h : Relation.EqvGen (· ≤ ·) a b) : Relation.EqvGen (· ≤ ·) (F a) (F b) := by
  induction h with
  | rel a b hab => exact hF a b hab
  | refl a => exact .refl (F a)
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem categorical_of_upward_labels [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root) {A : Set X} (labels : A → X)
    (hlabels : ∀ a b : A, a ≤ b → labels a = labels b)
    (hup : ∀ a : A, a.val ≤ labels a) : Categorical A := by
  classical
  let labelMap (f : X → X) : A →o X :=
    ⟨f ∘ labels, fun a b hab => (congrArg f (hlabels a b hab)).le⟩
  let patched (P : Finset X) (x : X) : X := if x ∈ P then root else x
  have connPatch (P : Finset X) :
      Relation.EqvGen (· ≤ ·) (labelMap id) (labelMap (patched P)) := by
    induction P using Finset.induction_on with
    | empty =>
      have he : patched ∅ = id := by funext x; simp [patched]
      rw [he]
      exact .refl _
    | @insert x P hx ih =>
      let edit (v y : X) : X := if y = x then v else patched P y
      have hstart : edit x = patched P := by
        funext y
        by_cases hy : y = x
        · subst y; simp [edit, patched, hx]
        · simp [edit, hy]
      have hend : edit root = patched (insert x P) := by
        funext y
        by_cases hy : y = x <;> simp [edit, patched, hy]
      have hedit := mapFence (fun v => labelMap (edit v))
        (fun a b hab => .rel _ _ (by
          intro y
          change edit a (labels y) ≤ edit b (labels y)
          by_cases hy : labels y = x <;> simp [edit, hy, hab])) (hconn x)
      rw [hstart, hend] at hedit
      exact .trans _ _ _ ih hedit
  have hfinal : labelMap (patched Finset.univ) = OrderHom.const A root := by
    apply OrderHom.ext
    funext x
    change patched Finset.univ (labels x) = root
    simp [patched]
  have hstart : (OrderEmbedding.subtype A).toOrderHom ≤ labelMap id := hup
  exact ⟨root, .trans _ _ _ (.rel _ _ hstart) (hfinal ▸ connPatch Finset.univ)⟩

private def lowerPiece (S : Finset X) : Set X := {x | IsMin x ∨ x ∈ S}
private def upperPiece (S : Finset X) : Set X := {x | IsMax x ∨ x ∈ S}

private theorem lowerPiece_categorical [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root) (S : Finset X)
    (h : (∃ c : X, ∀ s ∈ S, s ≤ c) ∨
      ∀ a b : X, a ∈ S → b ∈ S → ∀ y : X, y ≤ a → y ≤ b → a = b) :
    Categorical (lowerPiece S) := by
  classical
  let sees (x : X) : Prop := ∃ s ∈ S, x ≤ s
  have below (x y : lowerPiece S) (hxy : x ≤ y) : sees y.val → sees x.val :=
    fun ⟨s, hs, hys⟩ => ⟨s, hs, (show x.val ≤ y.val from hxy).trans hys⟩
  have isolated (x y : lowerPiece S) (hxy : x ≤ y) (hy : ¬ sees y.val) : x = y := by
    have hymin : IsMin y.val := y.property.resolve_right (fun hs => hy ⟨_, hs, le_rfl⟩)
    exact Subtype.ext (hymin.eq_of_le hxy)
  rcases h with ⟨c, hc⟩ | hu
  · let labels (x : lowerPiece S) := if sees x.val then c else x.val
    apply categorical_of_upward_labels root hconn labels
    · intro x y hxy
      by_cases hy : sees y.val
      · simp [labels, hy, below x y hxy hy]
      · rw [isolated x y hxy hy]
    · intro x
      by_cases hx : sees x.val
      · obtain ⟨s, hs, hxs⟩ := hx
        simpa [labels, show sees x.val from ⟨s, hs, hxs⟩] using hxs.trans (hc s hs)
      · simp [labels, hx]
  · let labels (x : lowerPiece S) := if hx : sees x.val then hx.choose else x.val
    apply categorical_of_upward_labels root hconn labels
    · intro x y hxy
      by_cases hy : sees y.val
      · have hx := below x y hxy hy
        have hchoose := hu _ _ hx.choose_spec.1 hy.choose_spec.1
          x.val hx.choose_spec.2 ((show x.val ≤ y.val from hxy).trans hy.choose_spec.2)
        simpa [labels, hx, hy] using hchoose
      · rw [isolated x y hxy hy]
    · intro x
      by_cases hx : sees x.val
      · simpa [labels, hx] using hx.choose_spec.2
      · simp [labels, hx]

private theorem upperPiece_categorical [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root) (S : Finset X)
    (h : (∃ c : X, ∀ s ∈ S, c ≤ s) ∨
      ∀ a b : X, a ∈ S → b ∈ S → ∀ y : X, a ≤ y → b ≤ y → a = b) :
    Categorical (upperPiece S) := by
  have hconn' (x : Xᵒᵈ) : Relation.EqvGen (· ≤ ·) x root :=
    mapFence (A := X) (B := Xᵒᵈ) OrderDual.toDual
      (fun a b hab => .symm _ _ (.rel _ _ hab)) (hconn x)
  obtain ⟨c, hc⟩ := lowerPiece_categorical (X := Xᵒᵈ) root hconn' S h
  refine ⟨c, ?_⟩
  exact mapFence (fun (f : lowerPiece (X := Xᵒᵈ) S →o Xᵒᵈ) => f.dual)
    (fun a b hab => .symm _ _ (.rel _ _ hab)) hc

private theorem partition_subdivides [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root) (S T : Finset X)
    (hcov : ∀ x : X, ¬ IsMin x → ¬ IsMax x → x ∈ S ∨ x ∈ T)
    (hS : (∃ c : X, ∀ s ∈ S, s ≤ c) ∨
      ∀ a b : X, a ∈ S → b ∈ S → ∀ y : X, y ≤ a → y ≤ b → a = b)
    (hT : (∃ c : X, ∀ t ∈ T, c ≤ t) ∨
      ∀ a b : X, a ∈ T → b ∈ T → ∀ y : X, a ≤ y → b ≤ y → a = b) :
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains X)) 2 := by
  apply hasCategoricalCover_double_subdivision
    (lowerPiece_categorical root hconn S hS) (upperPiece_categorical root hconn T hT)
  intro x
  by_cases hlo : IsMin x
  · exact Or.inl (Or.inl hlo)
  by_cases hhi : IsMax x
  · exact Or.inr (Or.inl hhi)
  rcases hcov x hlo hhi with hx | hx
  · exact Or.inl (Or.inr hx)
  · exact Or.inr (Or.inr hx)

/-- A connected finite poset with at most three intermediate vertices has a
categorical two-cover at the second subdivision. -/
theorem two_cover_of_at_most_three_intermediate [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root)
    (I : Finset X) (hI : ∀ x, ¬ IsMin x → ¬ IsMax x → x ∈ I) (hcard : I.card ≤ 3) :
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains X)) 2 := by
  classical
  by_cases hsmall : I.card ≤ 1
  · apply partition_subdivides root hconn I ∅
    · exact fun x hx hy => Or.inl (hI x hx hy)
    · exact Or.inr fun a b ha hb _ _ _ => Finset.card_le_one.mp hsmall a ha b hb
    · exact Or.inl ⟨root, by simp⟩
  have hpair : 1 < I.card := Nat.lt_of_not_ge hsmall
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hpair
  let pair : Finset X := {a, b}
  let rem := I \ pair
  have hsub : pair ⊆ I := by
    intro x hx
    rcases (show x = a ∨ x = b by simpa [pair] using hx) with rfl | rfl
    · exact ha
    · exact hb
  have hrem : rem.card ≤ 1 := by
    have hpair : pair.card = 2 := by simp [pair, hab]
    have h := Finset.card_sdiff_of_subset hsub
    change rem.card = I.card - pair.card at h
    omega
  have hcov (x : X) (hx : ¬ IsMin x) (hy : ¬ IsMax x) : x ∈ pair ∨ x ∈ rem := by
    by_cases hxp : x ∈ pair
    · exact Or.inl hxp
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hI x hx hy, hxp⟩)
  by_cases hub : ∃ c : X, a ≤ c ∧ b ≤ c
  · obtain ⟨c, ha, hb⟩ := hub
    apply partition_subdivides root hconn pair rem hcov
    · left
      refine ⟨c, ?_⟩
      intro x hx
      rcases (show x = a ∨ x = b by simpa [pair] using hx) with rfl | rfl
      · exact ha
      · exact hb
    · exact Or.inr fun p q hp hq _ _ _ => Finset.card_le_one.mp hrem p hp q hq
  · apply partition_subdivides root hconn rem pair (fun x hx hy => (hcov x hx hy).symm)
    · exact Or.inr fun p q hp hq _ _ _ => Finset.card_le_one.mp hrem p hp q hq
    · right
      intro p q hp hq y hpy hqy
      have hp' : p = a ∨ p = b := by simpa [pair] using hp
      have hq' : q = a ∨ q = b := by simpa [pair] using hq
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · rfl
      · exact (hub ⟨y, hpy, hqy⟩).elim
      · exact (hub ⟨y, hqy, hpy⟩).elim
      · rfl

private theorem pair_with_common_max [Fintype X] (I U : Finset X)
    (hcard : U.card < I.card * 2)
    (habove : ∀ a ∈ I, ∃ u ∈ U, ∃ v ∈ U, u ≠ v ∧ a ≤ u ∧ a ≤ v) :
    ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ c ∈ U, a ≤ c ∧ b ≤ c := by
  classical
  by_contra h
  let fst (a : I) : X := (habove a.val a.property).choose
  let snd (a : I) : X := (habove a.val a.property).choose_spec.2.choose
  let place (pair : I × Bool) : X := if pair.2 then fst pair.1 else snd pair.1
  have hfst (a : I) : fst a ∈ U ∧ a.val ≤ fst a := by
    have h := (habove a.val a.property).choose_spec
    exact ⟨h.1, h.2.choose_spec.2.2.1⟩
  have hsnd (a : I) : snd a ∈ U ∧ a.val ≤ snd a := by
    have h := (habove a.val a.property).choose_spec.2.choose_spec
    exact ⟨h.1, h.2.2.2⟩
  have hdiff (a : I) : fst a ≠ snd a :=
    (habove a.val a.property).choose_spec.2.choose_spec.2.1
  have hplace (p : I × Bool) : place p ∈ U ∧ p.1.val ≤ place p := by
    cases hp : p.2 <;> simp [place, hp, hfst, hsnd]
  have inj : Function.Injective place := by
    rintro ⟨a, i⟩ ⟨b, j⟩ heq
    have ha := hplace (a, i)
    have hb := hplace (b, j)
    have hab : a = b := by
      apply Subtype.ext
      by_contra hn
      exact h ⟨a, a.property, b, b.property, hn, place (a, i), ha.1,
        ha.2, heq.symm ▸ hb.2⟩
    subst b
    cases i <;> cases j
    · rfl
    · exact (hdiff a (by simpa [place] using heq.symm)).elim
    · exact (hdiff a (by simpa [place] using heq)).elim
    · rfl
  have hcount := Finset.card_le_card_of_injOn place
    (s := Finset.univ) (t := U) (fun p _ => (hplace p).1) inj.injOn
  have hcount' : I.card * 2 ≤ U.card := by
    simpa [Fintype.card_prod] using hcount
  omega

/-- Four intermediate vertices admit a categorical two-cover at the second
subdivision if there are at most three minima and at most seven maxima,
and each intermediate vertex lies between two extrema on each side. -/
theorem two_cover_of_four_intermediate [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root)
    (I L U : Finset X) (hI : ∀ x, ¬ IsMin x → ¬ IsMax x → x ∈ I)
    (hcard : I.card = 4) (hL : L.card ≤ 3) (hU : U.card ≤ 7)
    (hlow : ∀ a ∈ I, ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧ x ≤ a ∧ y ≤ a)
    (hhigh : ∀ a ∈ I, ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ a ≤ x ∧ a ≤ y) :
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains X)) 2 := by
  classical
  obtain ⟨a, ha, b, hb, hab, c, _, hac, hbc⟩ :=
    pair_with_common_max I U (by omega) hhigh
  let pair : Finset X := {a, b}
  let rem := I \ pair
  have hsub : pair ⊆ I := by
    intro x hx
    rcases (show x = a ∨ x = b by simpa [pair] using hx) with rfl | rfl
    · exact ha
    · exact hb
  have hrem : rem.card = 2 := by
    have hp : pair.card = 2 := by simp [pair, hab]
    have h := Finset.card_sdiff_of_subset hsub
    change rem.card = I.card - pair.card at h
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (show 1 < rem.card by omega)
  have hpqRem : rem = {p, q} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases (show x = p ∨ x = q by simpa using hx) with rfl | rfl
      · exact hp
      · exact hq
    · simpa [hpq] using hrem.le
  let low (x : X) := L.filter (· ≤ x)
  have lowCard (x : X) (hx : x ∈ rem) : 2 ≤ (low x).card := by
    obtain ⟨u, hu, v, hv, huv, hux, hvx⟩ := hlow x (Finset.mem_sdiff.mp hx).1
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hux⟩,
      v, Finset.mem_filter.mpr ⟨hv, hvx⟩, huv⟩
  have hUnion : (low p ∪ low q).card ≤ L.card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hsum := Finset.card_inter_add_card_union (low p) (low q)
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (low p ∩ low q).card by
    have := lowCard p hp
    have := lowCard q hq
    omega)
  have hdlo := Finset.mem_inter.mp hd
  apply partition_subdivides root hconn pair rem
  · intro x hx hy
    by_cases hxp : x ∈ pair
    · exact Or.inl hxp
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hI x hx hy, hxp⟩)
  · left
    refine ⟨c, ?_⟩
    intro x hx
    rcases (show x = a ∨ x = b by simpa [pair] using hx) with rfl | rfl
    · exact hac
    · exact hbc
  · left
    refine ⟨d, ?_⟩
    intro x hx
    rcases (show x = p ∨ x = q by simpa [hpqRem] using hx) with rfl | rfl
    · exact (Finset.mem_filter.mp hdlo.1).2
    · exact (Finset.mem_filter.mp hdlo.2).2

/-- With five intermediate points, four upper extrema force a triple with a
common upper bound. The complementary pair shares a lower bound among at most
three lower extrema. The resulting partition gives a categorical two-cover. -/
theorem two_cover_of_five_intermediate [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root)
    (I L U : Finset X) (hI : ∀ x, ¬ IsMin x → ¬ IsMax x → x ∈ I)
    (hcard : I.card = 5) (hL : L.card ≤ 3) (hU : U.card ≤ 4)
    (hlow : ∀ a ∈ I, ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧ x ≤ a ∧ y ≤ a)
    (hhigh : ∀ a ∈ I, ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ a ≤ x ∧ a ≤ y) :
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains X)) 2 := by
  classical
  let fst (a : I) : X := (hhigh a.val a.property).choose
  let snd (a : I) : X := (hhigh a.val a.property).choose_spec.2.choose
  let place (pair : I × Bool) : X := if pair.2 then fst pair.1 else snd pair.1
  have hfst (a : I) : fst a ∈ U ∧ a.val ≤ fst a := by
    have h := (hhigh a.val a.property).choose_spec
    exact ⟨h.1, h.2.choose_spec.2.2.1⟩
  have hsnd (a : I) : snd a ∈ U ∧ a.val ≤ snd a := by
    have h := (hhigh a.val a.property).choose_spec.2.choose_spec
    exact ⟨h.1, h.2.2.2⟩
  have hdiff (a : I) : fst a ≠ snd a :=
    (hhigh a.val a.property).choose_spec.2.choose_spec.2.1
  have hplace (p : I × Bool) : place p ∈ U ∧ p.1.val ≤ place p := by
    cases hp : p.2 <;> simp [place, hp, hfst, hsnd]
  have hthreshold : U.card * 2 < (Finset.univ : Finset (I × Bool)).card := by
    simp [Fintype.card_prod, hcard]
    omega
  obtain ⟨c, _, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (f := place) (fun p _ => (hplace p).1) hthreshold
  let fiber := (Finset.univ : Finset (I × Bool)).filter (fun p => place p = c)
  let project (p : I × Bool) := p.1.val
  have hinj : Set.InjOn project fiber := by
    rintro ⟨a, i⟩ hi ⟨b, j⟩ hj heq
    have hab : a = b := Subtype.ext heq
    subst b
    have hp : place (a, i) = place (a, j) :=
      (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    cases i <;> cases j
    · rfl
    · exact (hdiff a (by simpa [place] using hp.symm)).elim
    · exact (hdiff a (by simpa [place] using hp)).elim
    · rfl
  have himage : 3 ≤ (fiber.image project).card := by
    rw [Finset.card_image_of_injOn hinj]
    exact hc
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq himage
  have hS' : ∀ x ∈ S, x ∈ I ∧ x ≤ c := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (hS hx)
    exact ⟨p.1.property, (Finset.mem_filter.mp hp).2 ▸ (hplace p).2⟩
  let T := I \ S
  have hTcard : T.card = 2 := by
    have h := Finset.card_sdiff_of_subset (show S ⊆ I from fun _ hx => (hS' _ hx).1)
    change T.card = I.card - S.card at h
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  have hTpq : T = {p, q} := by
    symm
    apply Finset.eq_of_subset_of_card_le _ (by simpa [hpq] using hTcard.le)
    intro x hx
    rcases (show x = p ∨ x = q by simpa using hx) with rfl | rfl <;> assumption
  let below (x : X) := L.filter (· ≤ x)
  have hBelow (x : X) (hx : x ∈ T) : 2 ≤ (below x).card := by
    obtain ⟨u, hu, v, hv, huv, hux, hvx⟩ := hlow x (Finset.mem_sdiff.mp hx).1
    exact Finset.one_lt_card.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hux⟩,
      v, Finset.mem_filter.mpr ⟨hv, hvx⟩, huv⟩
  have hUnion : (below p ∪ below q).card ≤ L.card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hCount := Finset.card_inter_add_card_union (below p) (below q)
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (below p ∩ below q).card by
    have := hBelow p hp
    have := hBelow q hq
    omega)
  have hdl := Finset.mem_inter.mp hd
  apply partition_subdivides root hconn S T
  · intro x hx hy
    by_cases hxs : x ∈ S
    · exact Or.inl hxs
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hI x hx hy, hxs⟩)
  · exact Or.inl ⟨c, fun x hx => (hS' x hx).2⟩
  · left
    refine ⟨d, ?_⟩
    intro x hx
    rcases (show x = p ∨ x = q by simpa [hTpq] using hx) with rfl | rfl
    · exact (Finset.mem_filter.mp hdl.1).2
    · exact (Finset.mem_filter.mp hdl.2).2

private theorem min_below [Finite X] (x : X) : ∃ p : X, IsMin p ∧ p ≤ x := by
  obtain ⟨p, hpx, hp⟩ := Finite.exists_le_minimal (p := fun y : X => y ≤ x)
    (show x ≤ x from le_rfl)
  exact ⟨p, fun _ h => hp.2 (h.trans hpx) h, hpx⟩

/-- A finite poset with no down beat points has at least two minima below
each of its nonminimal vertices. -/
theorem two_minima_below_of_no_down_beat [Finite X]
    (hbeat : ∀ x : X, ¬ ∃ p : X, p < x ∧ ∀ y < x, y ≤ p)
    {x : X} (hx : ¬ IsMin x) :
    ∃ p q : X, IsMin p ∧ IsMin q ∧ p ≠ q ∧ p ≤ x ∧ q ≤ x := by
  obtain ⟨p, hmin, hpx⟩ := min_below x
  by_contra h
  have onlyMin (y : X) (hy : IsMin y) (hyx : y ≤ x) : y = p := by
    by_contra hne
    exact h ⟨p, y, hmin, hy, (fun e => hne e.symm), hpx, hyx⟩
  have hlt : p < x := lt_of_le_of_ne hpx (fun e => hx (e ▸ hmin))
  obtain ⟨q, hqx, hq⟩ := Finite.exists_le_minimal
    (p := fun y : X => p < y ∧ y ≤ x) ⟨hlt, le_rfl⟩
  apply hbeat q
  refine ⟨p, hq.1.1, ?_⟩
  intro y hy
  obtain ⟨m, hm, hmy⟩ := min_below y
  have hmp := onlyMin m hm (hmy.trans (hy.le.trans hqx))
  have hpy : p ≤ y := hmp ▸ hmy
  by_contra hnot
  have hpyl : p < y := lt_of_le_not_ge hpy hnot
  exact (not_le_of_gt hy) (hq.2 ⟨hpyl, hy.le.trans hqx⟩ hy.le)

/-- In a finite connected poset with at most two minima and no down beat
point, two categorical pieces cover its second subdivision. -/
theorem two_cover_of_at_most_two_minima [Fintype X] (root : X)
    (L : Finset X) (hL : ∀ x : X, x ∈ L ↔ IsMin x) (hcard : L.card ≤ 2)
    (hbeat : ∀ x : X, ¬ ∃ p : X, p < x ∧ ∀ y < x, y ≤ p) :
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains X)) 2 := by
  classical
  obtain ⟨p, hp, _⟩ := min_below root
  have hpm := (hL p).mpr hp
  by_cases hsingle : L.card ≤ 1
  · have least (x : X) : p ≤ x := by
      obtain ⟨q, hq, hqx⟩ := min_below x
      have e := Finset.card_le_one.mp hsingle q ((hL q).mpr hq) p hpm
      exact e ▸ hqx
    apply hasCategoricalCover_double_subdivision (A := Set.univ) (B := ∅)
    · exact ⟨p, .symm _ _ (.rel _ _ fun x => least x.val)⟩
    · exact ⟨p, .rel _ _ fun x => x.property.elim⟩
    · exact fun _ => Or.inl trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hsingle)
  have hpair : L = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
      · exact ha
      · exact hb
    · simpa [hab] using hcard
  have above (x : X) (hx : x ≠ a) : b ≤ x := by
    by_cases hmin : IsMin x
    · have hmem := (hL x).mpr hmin
      rw [hpair] at hmem
      have h := (show x = a ∨ x = b by simpa using hmem).resolve_left hx
      exact h.symm ▸ le_rfl
    · obtain ⟨c, d, hc, hd, hne, hcx, hdx⟩ :=
        two_minima_below_of_no_down_beat hbeat hmin
      have hcm := (hL c).mpr hc
      have hdm := (hL d).mpr hd
      rw [hpair] at hcm hdm
      rcases (show c = a ∨ c = b by simpa using hcm) with hca | hcb
      · have hdb := (show d = a ∨ d = b by simpa using hdm).resolve_left
          (fun hda => hne (hca.trans hda.symm))
        exact hdb ▸ hdx
      · exact hcb ▸ hcx
  apply hasCategoricalCover_double_subdivision (A := {a}) (B := {x | x ≠ a})
  · use a
    exact .rel _ _ fun x => (Set.mem_singleton_iff.mp x.property).le
  · use b
    exact .symm _ _ (.rel _ _ fun x => above x.val x.property)
  · intro x
    by_cases h : x = a
    · exact Or.inl h
    · exact Or.inr h

/-- A connected beat-point-free poset on at most fourteen vertices has a
two-cover after two subdivisions if at most seven vertices lie outside
its set of maximal points and it has at least two maximal points. -/
theorem two_cover_of_at_most_seven_nonmaximal [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root)
    (hdown : ∀ x : X, ¬ ∃ p : X, p < x ∧ ∀ y < x, y ≤ p)
    (hup : ∀ x : X, ¬ ∃ p : X, x < p ∧ ∀ y, x < y → p ≤ y)
    (hn : Fintype.card X ≤ 14)
    (U : Finset X) (hU : ∀ x : X, x ∈ U ↔ IsMax x) (htwoMax : 2 ≤ U.card)
    (hOutside : Fintype.card X ≤ U.card + 7) :
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains X)) 2 := by
  classical
  let L := Finset.univ.filter (fun x : X => IsMin x)
  let I := Finset.univ \ (L ∪ U)
  have hL (x : X) : x ∈ L ↔ IsMin x := by simp [L]
  have hI (x : X) : x ∈ I ↔ ¬ IsMin x ∧ ¬ IsMax x := by
    simp [I, hL, hU, not_or]
  by_cases htwo : L.card ≤ 2
  · exact two_cover_of_at_most_two_minima root L hL htwo hdown
  have hdisjoint : Disjoint L U := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxL hxU
    have hmin := (hL x).mp hxL
    have hmax := (hU x).mp hxU
    have isolated {a b : X} (h : Relation.EqvGen (· ≤ ·) a b) : a = x ↔ b = x := by
      induction h with
      | rel a b hab =>
        constructor
        · rintro rfl
          exact le_antisymm (hmax hab) hab
        · rintro rfl
          exact le_antisymm hab (hmin hab)
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have hroot : root = x := (isolated (hconn x)).mp rfl
    have hone : U.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact ((isolated (hconn a)).mpr hroot).trans ((isolated (hconn b)).mpr hroot).symm
    omega
  have hTotal : I.card + (L.card + U.card) = Fintype.card X := by
    have hc := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (L ∪ U))
    simpa [I, Finset.card_union_of_disjoint hdisjoint] using hc
  by_cases hthree : I.card ≤ 3
  · exact two_cover_of_at_most_three_intermediate root hconn I
      (fun x hx hy => (hI x).mpr ⟨hx, hy⟩) hthree
  apply two_cover_of_four_intermediate root hconn I L U
    (fun x hx hy => (hI x).mpr ⟨hx, hy⟩) (by omega) (by omega) (by omega)
  · intro a ha
    obtain ⟨x, y, hx, hy, hne, hxa, hya⟩ :=
      two_minima_below_of_no_down_beat hdown ((hI a).mp ha).1
    exact ⟨x, (hL x).mpr hx, y, (hL y).mpr hy, hne, hxa, hya⟩
  · intro a ha
    obtain ⟨x, y, hx, hy, hne, hax, hay⟩ :=
      two_minima_below_of_no_down_beat (X := Xᵒᵈ) hup ((hI a).mp ha).2
    exact ⟨x, (hU x).mpr hx, y, (hU y).mpr hy, hne, hax, hay⟩

/-- A connected beat-point-free poset with at most eleven points and at least
four maximal points has a two-piece categorical cover after two subdivisions.
This is the connected large-ordinary-category case of Conjecture 6.1. -/
theorem two_cover_of_at_most_eleven_and_four_maxima [Fintype X] (root : X)
    (hconn : ∀ x, Relation.EqvGen (· ≤ ·) x root)
    (hdown : ∀ x : X, ¬ ∃ p : X, p < x ∧ ∀ y < x, y ≤ p)
    (hup : ∀ x : X, ¬ ∃ p : X, x < p ∧ ∀ y, x < y → p ≤ y)
    (hn : Fintype.card X ≤ 11)
    (U : Finset X) (hU : ∀ x : X, x ∈ U ↔ IsMax x) (hfour : 4 ≤ U.card) :
    HasCategoricalCover (PartialOrder.NonemptyFiniteChains
      (PartialOrder.NonemptyFiniteChains X)) 2 := by
  exact two_cover_of_at_most_seven_nonmaximal root hconn hdown hup (by omega) U hU
    (by omega) (by omega)

end D5.S3.Topology.SmallPosetSubdivisionCategory
