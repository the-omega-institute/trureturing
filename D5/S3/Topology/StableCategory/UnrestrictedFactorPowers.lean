/- GID: D5/S3/Topology/StableCategory/UnrestrictedFactorPowers
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/UnrestrictedFactorPowers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-step categorical cover sizes are unbounded on finite powers. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Choose
import D5.S3.Topology.StableCategory.HalesJewettCategoricalCover
import D5.S3.Topology.SubdivisionCategoricalCover

/-! # Categorical covers of singly subdivided finite powers -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.UnrestrictedFactorPowers

open ConnectedCategoryGraft (HasCategoricalCover)
open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open Relation (EqvGen)

private structure Padded (X : Type*) (h : ℕ) where
  base : X
  rank : Fin h

private instance {X : Type*} [Finite X] {h : ℕ} : Finite (Padded X h) :=
  Finite.of_injective (fun a : Padded X h => (a.base, a.rank)) (by
    rintro ⟨x, i⟩ ⟨y, j⟩ heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    rfl)

section Padding

variable {X : Type*} [PartialOrder X] {h : ℕ}

private abbrev paddedLE (a b : Padded X h) : Prop :=
  a.base ≤ b.base ∧ (a.rank < b.rank ∨ a = b)

private instance : PartialOrder (Padded X h) where
  le := paddedLE
  le_refl _ := ⟨le_rfl, Or.inr rfl⟩
  le_trans a b c hab hbc := by
    change paddedLE a b at hab
    change paddedLE b c at hbc
    rcases hab.2 with hab' | rfl
    · rcases hbc.2 with hbc' | rfl
      · exact ⟨hab.1.trans hbc.1, Or.inl (hab'.trans hbc')⟩
      · exact hab
    · exact hbc
  le_antisymm a b hab hba := by
    change paddedLE a b at hab
    change paddedLE b a at hba
    rcases hab.2 with hab' | heq
    · rcases hba.2 with hba' | heq
      · exact (lt_asymm hab' hba').elim
      · exact heq.symm
    · exact heq

private theorem padded_le {a b : Padded X h} :
    a ≤ b ↔ a.base ≤ b.base ∧ (a.rank < b.rank ∨ a = b) := Iff.rfl

private theorem padded_le_same (x : X) {i j : Fin h} (hij : i ≤ j) :
    (⟨x, i⟩ : Padded X h) ≤ ⟨x, j⟩ := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact padded_le.mpr ⟨le_rfl, Or.inl hlt⟩
  · exact le_rfl

private def project : Padded X h →o X :=
  ⟨Padded.base, fun _ _ hab => (padded_le.mp hab).1⟩

private def rank : Padded X h →o Fin h :=
  ⟨Padded.rank, by
    intro a b hab
    rcases (padded_le.mp hab).2 with hlt | rfl
    · exact hlt.le
    · exact le_rfl⟩

private def sectionMap (t : X → Fin h) (ht : StrictMono t) : X →o Padded X h :=
  ⟨fun x => ⟨x, t x⟩, by
    intro x y hxy
    rcases lt_or_eq_of_le hxy with hlt | rfl
    · exact padded_le.mpr ⟨hxy, Or.inl (ht hlt)⟩
    · exact le_rfl⟩

private def raiseRank (t : X → Fin h) (ht : StrictMono t) : Padded X h →o Padded X h :=
  ⟨fun a => ⟨a.base, max a.rank (t a.base)⟩, by
    intro a b hab
    change (⟨a.base, max a.rank (t a.base)⟩ : Padded X h) ≤
      ⟨b.base, max b.rank (t b.base)⟩
    rcases padded_le.mp hab with ⟨hbase, hlt | rfl⟩
    · rcases lt_or_eq_of_le hbase with hbase' | heq
      · exact padded_le.mpr ⟨hbase, Or.inl (max_lt_iff.mpr
          ⟨hlt.trans_le (le_max_left _ _), (ht hbase').trans_le (le_max_right _ _)⟩)⟩
      · rw [heq]
        exact padded_le_same b.base (max_le_max hlt.le le_rfl)
    · exact le_rfl⟩

private theorem id_le_raiseRank (t : X → Fin h) (ht : StrictMono t) :
    (OrderHom.id : Padded X h →o Padded X h) ≤ raiseRank t ht :=
  fun a => padded_le_same a.base (le_max_left _ _)

private theorem section_project_le_raiseRank (t : X → Fin h) (ht : StrictMono t) :
    (sectionMap t ht).comp project ≤ raiseRank t ht :=
  fun a => padded_le_same a.base (le_max_right _ _)

private theorem exists_rank [Finite X] : ∃ h : ℕ, ∃ t : X → Fin h, StrictMono t := by
  classical
  letI := Fintype.ofFinite X
  let lower (x : X) : Finset X := Finset.univ.filter (· ≤ x)
  have hmem (x z : X) : z ∈ lower x ↔ z ≤ x := by simp [lower]
  refine ⟨Fintype.card X + 1,
    fun x => ⟨(lower x).card, Nat.lt_succ_of_le (Finset.card_le_univ _)⟩, ?_⟩
  intro x y hxy
  change (lower x).card < (lower y).card
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro z hz
    exact (hmem y z).mpr (((hmem x z).mp hz).trans hxy.le)
  · intro heq
    have hy : y ∈ lower y := (hmem y y).mpr le_rfl
    rw [← heq] at hy
    exact (not_le_of_gt hxy) ((hmem x y).mp hy)

/-- At each rank use the greatest chain member at or below it, falling back to
the first chain member when the rank precedes the chain. -/
private theorem extend_chain (C : NonemptyFiniteChains (Padded X h)) :
    ∃ e : Fin h ↪o Padded X h,
      (∀ i, rank (e i) = i) ∧ ∀ a ∈ C.finset, a ∈ Set.range e := by
  classical
  obtain ⟨first, hfirst, hmin⟩ := Finset.exists_min_image C.finset Padded.rank C.nonempty
  have pick (i : Fin h) : ∃ a ∈ C.finset,
      (∀ z ∈ C.finset, z.rank ≤ i → z.rank ≤ a.rank) ∧
      (a.rank ≤ i ∨ ∀ z ∈ C.finset, a.rank ≤ z.rank) := by
    let below := C.finset.filter (fun z => z.rank ≤ i)
    have mem_below (z : Padded X h) : z ∈ below ↔ z ∈ C.finset ∧ z.rank ≤ i :=
      Finset.mem_filter
    by_cases hbelow : below.Nonempty
    · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image below Padded.rank hbelow
      exact ⟨a, ((mem_below a).mp ha).1,
        fun z hz hzi => hmax z ((mem_below z).mpr ⟨hz, hzi⟩),
        Or.inl ((mem_below a).mp ha).2⟩
    · refine ⟨first, hfirst, ?_, Or.inr hmin⟩
      exact fun z hz hzi => (hbelow ⟨z, (mem_below z).mpr ⟨hz, hzi⟩⟩).elim
  choose chosen hchosen hspec using pick
  have chain_le {a b : Padded X h} (ha : a ∈ C.finset) (hb : b ∈ C.finset)
      (hr : a.rank ≤ b.rank) : a ≤ b := by
    rcases C.comparable ⟨a, ha⟩ ⟨b, hb⟩ with hab | hba
    · exact hab
    · change b ≤ a at hba
      rcases (padded_le.mp hba).2 with hlt | heq
      · exact ((not_lt_of_ge hr) hlt).elim
      · exact heq.symm.le
  have chosen_mono : Monotone chosen := by
    intro i j hij
    apply chain_le (hchosen i) (hchosen j)
    rcases (hspec i).2 with hi | hi
    · exact (hspec j).1 _ (hchosen i) (hi.trans hij)
    · exact hi _ (hchosen j)
  let f (i : Fin h) : Padded X h := ⟨(chosen i).base, i⟩
  have hf : Monotone f := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact padded_le.mpr ⟨project.monotone (chosen_mono hij), Or.inl hlt⟩
    · exact le_rfl
  let e : Fin h ↪o Padded X h := OrderEmbedding.ofMapLEIff f (fun i j =>
    ⟨fun hij => show rank (f i) ≤ rank (f j) from rank.monotone hij, fun hij => hf hij⟩)
  refine ⟨e, fun _ => rfl, ?_⟩
  intro a ha
  have ha_le : a.rank ≤ (chosen a.rank).rank := (hspec a.rank).1 a ha le_rfl
  have hchosen_le : (chosen a.rank).rank ≤ a.rank :=
    (hspec a.rank).2.elim id (fun hmin' => hmin' a ha)
  have heq : chosen a.rank = a := le_antisymm
    (chain_le (hchosen a.rank) ha hchosen_le) (chain_le ha (hchosen a.rank) ha_le)
  refine ⟨a.rank, ?_⟩
  change Padded.mk (chosen a.rank).base a.rank = a
  exact congrArg (fun z : Padded X h => Padded.mk z.base a.rank) heq

end Padding

private theorem map_fence {S T : Type*} [Preorder S] [Preorder T] {f : S → T}
    (hf : Monotone f) {a b : S} (h : EqvGen (· ≤ ·) a b) :
    EqvGen (· ≤ ·) (f a) (f b) := by
  induction h with
  | rel _ _ hle => exact .rel _ _ (hf hle)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem pullback_cover {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (p : P →o Q) (s : Q →o P)
    (h : EqvGen (· ≤ ·) (OrderHom.id : P →o P) (s.comp p))
    {k : ℕ} (cover : HasCategoricalCover Q k) : HasCategoricalCover P k := by
  obtain ⟨U, hU, hcover⟩ := cover
  let V (i : Fin k) : Set P := p ⁻¹' U i
  refine ⟨V, ?_, fun x => hcover (p x)⟩
  intro i
  refine ⟨fun _ _ hab hb => (hU i).1 (p.monotone hab) hb, ?_⟩
  obtain ⟨c, hc⟩ := (hU i).2
  let inc : V i →o P := ⟨Subtype.val, fun _ _ hxy => hxy⟩
  let pre : V i →o U i := ⟨fun x => ⟨p x.val, x.property⟩, fun _ _ hxy => p.monotone hxy⟩
  let lift (f : U i →o Q) : V i →o P := s.comp (f.comp pre)
  have hstart : EqvGen (· ≤ ·) inc (lift (OrderEmbedding.subtype (U i)).toOrderHom) := by
    have hrestr := map_fence (f := fun f : P →o P => f.comp inc)
      (fun _ _ hfg x => OrderHom.le_def.mp hfg (inc x)) h
    have hcomp : (s.comp p).comp inc = lift (OrderEmbedding.subtype (U i)).toOrderHom := by
      apply OrderHom.ext
      rfl
    rw [OrderHom.id_comp, hcomp] at hrestr
    exact hrestr
  have hlift := map_fence (f := lift)
    (fun _ _ hfg x => s.monotone (OrderHom.le_def.mp hfg (pre x))) hc
  have hend : lift (OrderHom.const (U i) c) = OrderHom.const (V i) (s c) := rfl
  rw [hend] at hlift
  exact ⟨s c, .trans _ _ _ hstart hlift⟩

private theorem chainMap_id {P : Type*} [PartialOrder P] :
    orderHomMap (OrderHom.id : P →o P) = OrderHom.id := by
  classical
  apply OrderHom.ext
  funext C
  apply NonemptyFiniteChains.ext
  exact Finset.image_id

private theorem chainMap_comp {P Q R : Type*} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : P →o Q) (g : Q →o R) :
    orderHomMap (g.comp f) = (orderHomMap g).comp (orderHomMap f) := by
  classical
  apply OrderHom.ext
  funext C
  apply NonemptyFiniteChains.ext
  change C.finset.image (g ∘ f) = (C.finset.image f).image g
  exact (Finset.image_image (f := f) (g := g)).symm

private theorem pullback_subdivided_cover {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [Finite P] (p : P →o Q) (s : Q →o P)
    (h : EqvGen (· ≤ ·) (OrderHom.id : P →o P) (s.comp p))
    {k : ℕ} (cover : HasCategoricalCover (NonemptyFiniteChains Q) k) :
    HasCategoricalCover (NonemptyFiniteChains P) k := by
  refine pullback_cover (orderHomMap p) (orderHomMap s) ?_ cover
  simpa only [chainMap_id, chainMap_comp] using SubdivisionCategoricalCover.subdivision_map_fence h

/-- If the first subdivision of a finite partial order has no one-piece
categorical lower cover, its singly subdivided finite powers have unbounded
categorical lower-cover size. -/
theorem exists_no_categorical_cover_of_no_one {X : Type*} [PartialOrder X] [Finite X]
    (noOne : ¬ HasCategoricalCover (NonemptyFiniteChains X) 1) (k : ℕ) :
    ∃ n : ℕ, ¬ HasCategoricalCover (NonemptyFiniteChains (Fin n → X)) k := by
  classical
  obtain ⟨h, t, ht⟩ := exists_rank (X := X)
  let Y := Padded X h
  let p : Y →o X := project
  let s : X →o Y := sectionMap t ht
  let m : Y →o Y := raiseRank t ht
  have hps : p.comp s = OrderHom.id := by
    apply OrderHom.ext
    rfl
  have noOneY : ¬ HasCategoricalCover (NonemptyFiniteChains Y) 1 := by
    intro cover
    apply noOne
    exact pullback_subdivided_cover s p (by rw [hps]; exact .refl _) cover
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Finite (NonemptyFiniteChains Y) :=
    Finite.of_injective (fun C : NonemptyFiniteChains Y => C.finset)
      (fun _ _ heq => NonemptyFiniteChains.ext heq)
  let letter (C : NonemptyFiniteChains Y) : Fin h ↪o Y := Classical.choose (extend_chain C)
  have letter_rank (C : NonemptyFiniteChains Y) (i : Fin h) : rank (letter C i) = i :=
    (Classical.choose_spec (extend_chain C)).1 i
  have letter_extend (C : NonemptyFiniteChains Y) :
      ∃ a : NonemptyFiniteChains Y, ∀ x ∈ C.finset, x ∈ Set.range (letter a) :=
    ⟨C, (Classical.choose_spec (extend_chain C)).2⟩
  obtain ⟨n, hn⟩ := HalesJewettCategoricalCover.exists_no_categorical_cover
    (X := Y) (A := NonemptyFiniteChains Y) rank letter letter_rank letter_extend noOneY k
  refine ⟨n, ?_⟩
  intro cover
  apply hn
  let pn : (Fin n → Y) →o (Fin n → X) := OrderHom.pi (fun i => p.comp (Pi.evalOrderHom i))
  let sn : (Fin n → X) →o (Fin n → Y) := OrderHom.pi (fun i => s.comp (Pi.evalOrderHom i))
  let mn : (Fin n → Y) →o (Fin n → Y) := OrderHom.pi (fun i => m.comp (Pi.evalOrderHom i))
  have hid : (OrderHom.id : (Fin n → Y) →o (Fin n → Y)) ≤ mn :=
    fun w i => id_le_raiseRank t ht (w i)
  have hsp : sn.comp pn ≤ mn :=
    fun w i => section_project_le_raiseRank t ht (w i)
  exact pullback_subdivided_cover pn sn (.trans _ _ _ (.rel _ _ hid) (.symm _ _ (.rel _ _ hsp)))
    cover

end D5.S3.Topology.StableCategory.UnrestrictedFactorPowers
