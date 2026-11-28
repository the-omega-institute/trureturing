/- GID: D5/S3/Topology/StableCategory/RelativeMaximaDoubleSubdivision
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/RelativeMaximaDoubleSubdivision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximal attachments admit two relative pieces at the second subdivision. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.DescendingClosureContiguity
import D5.S3.Topology.StableCategory.RelativeCoverNecessity
import D5.S3.Topology.SubdivisionCategoricalCover
import Mathlib.Data.Fintype.Powerset

/-!
# A common old region after adjoining maximal elements

After two ordinary subdivisions, two lower regions cover the ambient poset
and deform into the same old region while fixing every old flag.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StableCategory.RelativeMaximaDoubleSubdivision

open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open DescendingClosureContiguity (exists_relative_contiguity_of_le)
open MaximalChainCoverExtension (chainsAvoiding)
open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open Relation (EqvGen)
open RelativeCoverNecessity
  (FixedOrderMaps RelativeOrderFence singletonChain isMin_singletonChain
    adjoinTop le_adjoinTop singletonChain_le_adjoinTop)

variable {P : Type} [PartialOrder P]

private abbrev Flag (P : Type*) [PartialOrder P] :=
  NonemptyFiniteChains (NonemptyFiniteChains P)

private def liftedRegion {X : Type*} [PartialOrder X] (U : Set X) :
    Set (NonemptyFiniteChains X) :=
  {s | ∀ x ∈ s.finset, x ∈ U}

private theorem liftedRegion_lower {X : Type*} [PartialOrder X] (U : Set X) :
    IsLowerSet (liftedRegion U) :=
  fun _ _ h hs x hx => hs x (h hx)

section RelativeComparison

open private unionMap from D5.S3.Topology.SubdivisionCategoricalCover

/-- Lift a descending comparison by chain images, fixing each prescribed flag
on which the original comparison agrees at every member. -/
private theorem relative_fence_of_comparison {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    {A E : Set (NonemptyFiniteChains Y)} (lift : A →o NonemptyFiniteChains X)
    {f g : X →o Y} (hfg : f ≤ g) (rank : X → ℕ) (hrank : StrictMono rank)
    (bound : ℕ) (hbound : ∀ x, rank x ≤ bound)
    (hstart : ∀ s : A, (lift s).map g = s.val)
    (hagree : ∀ (s : A), s.val ∈ E → ∀ x ∈ (lift s).finset, f x = g x)
    (hland : ∀ s : A, (lift s).map f ∈ E) : RelativeOrderFence A E := by
  classical
  obtain ⟨F, hzero, hlast, hfix, _, hstep⟩ :=
    exists_relative_contiguity_of_le rank hrank g f (OrderHom.le_def.mp hfg) bound hbound
  have image_fixed (k : ℕ) (s : A) (hs : s.val ∈ E) : (lift s).map (F k) = s.val := by
    calc
      (lift s).map (F k) = (lift s).map g := by
        apply NonemptyFiniteChains.ext
        change (lift s).finset.image (F k) = (lift s).finset.image g
        exact Finset.image_congr (fun x hx => hfix k x (hagree s hs x hx))
      _ = s.val := hstart s
  let row (k : ℕ) : FixedOrderMaps A E :=
    ⟨(orderHomMap (F k)).comp lift, image_fixed k⟩
  let bridge (k : ℕ) : FixedOrderMaps A E :=
    ⟨(unionMap (F k) (F (k + 1)) (hstep k)).comp lift, by
      intro s hs
      apply NonemptyFiniteChains.ext
      change ((lift s).map (F k)).finset ∪ ((lift s).map (F (k + 1))).finset = s.val.finset
      rw [image_fixed k s hs, image_fixed (k + 1) s hs, Finset.union_idempotent]⟩
  have path (k : ℕ) :
      EqvGen (fun a b : FixedOrderMaps A E => a.val ≤ b.val) (row 0) (row k) := by
    induction k with
    | zero => exact .refl _
    | succ k ih =>
      have hup : (row k).val ≤ (bridge k).val := fun _ => Finset.subset_union_left
      have hdown : (row (k + 1)).val ≤ (bridge k).val := fun _ => Finset.subset_union_right
      exact .trans _ _ _ ih (.trans _ _ _ (.rel _ _ hup) (.symm _ _ (.rel _ _ hdown)))
  have initial : row 0 = FixedOrderMaps.inclusion A E := by
    apply Subtype.ext
    apply OrderHom.ext
    funext s
    change (lift s).map (F 0) = s.val
    rw [hzero]
    exact hstart s
  refine ⟨row (bound + 1), ?_, ?_⟩
  · rw [← initial]
    exact path (bound + 1)
  · intro s
    change (lift s).map (F (bound + 1)) ∈ E
    rw [hlast]
    exact hland s

end RelativeComparison

private def meetsOld (T : Set P) : Set (NonemptyFiniteChains P) :=
  {s | ∃ x ∈ s.finset, x ∉ T}

section MeetingFlags

open private restrictChains from D5.S3.Topology.SubdivisionCategoricalCover

private theorem meeting_flags_fence [Finite P] (T : Set P) :
    RelativeOrderFence (liftedRegion (meetsOld T)) (liftedRegion (chainsAvoiding T)) := by
  classical
  let := Fintype.ofFinite P
  let V := meetsOld T
  let A := liftedRegion V
  let E := liftedRegion (chainsAvoiding T)
  let lift : A →o NonemptyFiniteChains V := restrictChains V fun s => by
    obtain ⟨a, ha⟩ := s.val.nonempty
    exact ⟨a, ha, s.property a ha⟩
  let oldInclusion : (Tᶜ : Set P) →o P := (OrderEmbedding.subtype (Tᶜ : Set P)).toOrderHom
  let trim : V →o NonemptyFiniteChains (Tᶜ : Set P) :=
    { toFun := fun a =>
        { finset := a.val.finset.subtype (· ∈ (Tᶜ : Set P))
          nonempty := by
            obtain ⟨x, hx, hxT⟩ := a.property
            exact ⟨⟨x, hxT⟩, Finset.mem_subtype.mpr hx⟩
          comparable := by
            rintro ⟨x, hx⟩ ⟨y, hy⟩
            exact a.val.comparable ⟨x.val, Finset.mem_subtype.mp hx⟩
              ⟨y.val, Finset.mem_subtype.mp hy⟩ }
      monotone' := fun _ _ hab => Finset.subtype_mono hab }
  let f : V →o NonemptyFiniteChains P := (orderHomMap oldInclusion).comp trim
  let g : V →o NonemptyFiniteChains P := (OrderEmbedding.subtype V).toOrderHom
  have mem_lift (s : A) (a : V) : a ∈ (lift s).finset ↔ a.val ∈ s.val.finset := by
    change a ∈ s.val.finset.subtype (· ∈ V) ↔ _
    exact Finset.mem_subtype
  have mem_trim (a : V) (x : P) : x ∈ (f a).finset ↔ x ∈ a.val.finset ∧ x ∉ T := by
    change x ∈ ((trim a).map oldInclusion).finset ↔ _
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ a.val.finset.subtype (· ∈ (Tᶜ : Set P)) := hy
      exact ⟨Finset.mem_subtype.mp hy', y.property⟩
    · rintro ⟨hx, hxT⟩
      exact ⟨⟨x, hxT⟩, show ⟨x, hxT⟩ ∈ a.val.finset.subtype (· ∈ (Tᶜ : Set P)) from
        Finset.mem_subtype.mpr hx, rfl⟩
  have hdesc : f ≤ g := by
    intro a x hx
    exact ((mem_trim a x).mp hx).1
  have hstart (s : A) : (lift s).map g = s.val := by
    apply NonemptyFiniteChains.ext
    apply Finset.ext
    intro a
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (mem_lift s b).mp hb
    · intro ha
      exact ⟨⟨a, s.property a ha⟩, (mem_lift s ⟨a, s.property a ha⟩).mpr ha, rfl⟩
  have hagree (s : A) (hs : s.val ∈ E) (a : V) (ha : a ∈ (lift s).finset) : f a = g a := by
    apply NonemptyFiniteChains.ext
    apply Finset.ext
    intro x
    change x ∈ (f a).finset ↔ x ∈ a.val.finset
    exact (mem_trim a x).trans ⟨And.left, fun hx => ⟨hx, hs a.val ((mem_lift s a).mp ha) x hx⟩⟩
  have hland (s : A) : (lift s).map f ∈ E := by
    intro a ha x hx
    obtain ⟨b, _, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp ha
    exact ((mem_trim b x).mp hx).2
  let rank (a : V) : ℕ := a.val.finset.card
  have hrank : StrictMono rank := fun _ _ h => Finset.card_lt_card h
  have hbound (a : V) : rank a ≤ Fintype.card P := Finset.card_le_univ _
  exact relative_fence_of_comparison lift hdesc rank hrank _ hbound hstart hagree hland

end MeetingFlags

private def flagsContaining (t : P) : Set (Flag P) :=
  liftedRegion {a : NonemptyFiniteChains P | t ∈ a.finset}

private def maximaSide (T : Set P) : Set (Flag P) :=
  {s | s ∈ liftedRegion (chainsAvoiding T) ∨ ∃ t : T, s ∈ flagsContaining t.val}

private theorem eq_of_selected_mem {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    (a : NonemptyFiniteChains P) (t u : T) (ht : t.val ∈ a.finset)
    (hu : u.val ∈ a.finset) : t = u := by
  apply Subtype.ext
  rcases a.comparable ⟨t.val, ht⟩ ⟨u.val, hu⟩ with h | h
  · change t.val ≤ u.val at h
    exact le_antisymm h (hT t.val t.property h)
  · change u.val ≤ t.val at h
    exact le_antisymm (hT u.val u.property h) h

open scoped Classical in
private def comparablePair {X : Type*} [PartialOrder X] (a b : X) (hab : a ≤ b) :
    NonemptyFiniteChains X where
  finset := {a, b}
  nonempty := ⟨a, Finset.mem_insert_self _ _⟩
  comparable := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    change x ≤ y ∨ y ≤ x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl hab
    · exact Or.inr hab
    · exact Or.inl le_rfl

private theorem maxima_flags_fence {T : Set P} (hT : ∀ t ∈ T, IsMax t)
    (hlt : ∀ t : T, ∃ x : P, x < t.val) :
    RelativeOrderFence (maximaSide T) (liftedRegion (chainsAvoiding T)) := by
  classical
  let E := liftedRegion (chainsAvoiding T)
  let A := maximaSide T
  let J (t : T) := flagsContaining t.val
  have hE : IsLowerSet E := liftedRegion_lower (chainsAvoiding T)
  have hJ (t : T) : IsLowerSet (J t) :=
    liftedRegion_lower {a : NonemptyFiniteChains P | t.val ∈ a.finset}
  have new_excludes_old (t : T) {s : Flag P} (ht : s ∈ J t) : s ∉ E := by
    intro hs
    obtain ⟨a, ha⟩ := s.nonempty
    exact hs a ha t.val (ht a ha) t.property
  have same_maximum (t u : T) {s : Flag P} (ht : s ∈ J t) (hu : s ∈ J u) : t = u := by
    obtain ⟨a, ha⟩ := s.nonempty
    exact eq_of_selected_mem hT a t u (ht a ha) (hu a ha)
  let witness (s : A) (hs : s.val ∉ E) : ∃ t : T, s.val ∈ J t :=
    (show s.val ∈ E ∨ ∃ t : T, s.val ∈ J t from s.property).resolve_left hs
  let label (s : A) (hs : s.val ∉ E) : T := (witness s hs).choose
  have label_mem (s : A) (hs : s.val ∉ E) : s.val ∈ J (label s hs) :=
    (witness s hs).choose_spec
  -- A comparison of flags in this side takes place entirely in a single summand.
  let glue (f : ∀ t : T, J t →o Flag P) : FixedOrderMaps A E :=
    ⟨{
      toFun := fun s =>
        if hs : s.val ∈ E then s.val else f (label s hs) ⟨s.val, label_mem s hs⟩
      monotone' := by
        intro s u h
        have hsu : s.val ≤ u.val := h
        by_cases hs : s.val ∈ E <;> by_cases hu : u.val ∈ E
        · simpa only [dite_eq_left hs, dite_eq_left hu] using hsu
        · exact (new_excludes_old (label u hu) (hJ (label u hu) hsu (label_mem u hu)) hs).elim
        · exact (hs (hE hsu hu)).elim
        · simp only [dite_eq_right hs, dite_eq_right hu]
          have compare (t v : T) (ht : s.val ∈ J t) (hv : u.val ∈ J v) :
              f t ⟨s.val, ht⟩ ≤ f v ⟨u.val, hv⟩ := by
            have he := same_maximum t v ht (hJ v hsu hv)
            subst v
            exact (f t).monotone (show (⟨s.val, ht⟩ : J t) ≤ ⟨u.val, hv⟩ from hsu)
          exact compare _ _ (label_mem s hs) (label_mem u hu)
    }, fun _ hs => dite_eq_left hs⟩
  have glue_new (f : ∀ t : T, J t →o Flag P) (s : A) (hs : s.val ∉ E) :
      (glue f).val s = f (label s hs) ⟨s.val, label_mem s hs⟩ := dite_eq_right hs
  have glue_le {f g : ∀ t : T, J t →o Flag P} (h : ∀ t, f t ≤ g t) :
      (glue f).val ≤ (glue g).val := by
    intro s
    by_cases hs : s.val ∈ E
    · simpa only [(glue f).property s hs, (glue g).property s hs] using
        (le_rfl : s.val ≤ s.val)
    · rw [glue_new f s hs, glue_new g s hs]
      exact OrderHom.le_def.mp (h (label s hs)) _
  let incl (t : T) : J t →o Flag P := (OrderEmbedding.subtype (J t)).toOrderHom
  have glue_incl : glue incl = FixedOrderMaps.inclusion A E := by
    apply Subtype.ext
    apply OrderHom.ext
    funext s
    change (glue incl).val s = s.val
    by_cases hs : s.val ∈ E
    · exact (glue incl).property s hs
    · exact glue_new incl s hs
  let tip (t : T) := singletonChain t.val
  have tip_le (t : T) {a : NonemptyFiniteChains P} (ha : t.val ∈ a.finset) : tip t ≤ a :=
    Finset.singleton_subset_iff.mpr ha
  let insertTip (t : T) : J t →o Flag P :=
    { toFun := fun s =>
        { finset := insert (tip t) s.val.finset
          nonempty := ⟨_, Finset.mem_insert_self _ _⟩
          comparable := by
            rintro ⟨a, ha⟩ ⟨b, hb⟩
            change a ≤ b ∨ b ≤ a
            rcases Finset.mem_insert.mp ha with hat | ha
            · rcases Finset.mem_insert.mp hb with hbt | hb
              · exact Or.inl (hat.trans hbt.symm).le
              · exact Or.inl (hat.le.trans (tip_le t (s.property b hb)))
            · rcases Finset.mem_insert.mp hb with hbt | hb
              · exact Or.inr (hbt.le.trans (tip_le t (s.property a ha)))
              · exact s.val.comparable ⟨a, ha⟩ ⟨b, hb⟩ }
      monotone' := fun _ _ h => Finset.insert_subset_insert _ h }
  let constantRow (q : T → Flag P) (t : T) : J t →o Flag P := OrderHom.const _ (q t)
  let c (t : T) : P := (hlt t).choose
  have hc (t : T) : c t < t.val := (hlt t).choose_spec
  have hc_old (t : T) : c t ∉ T :=
    fun h => (hc t).not_ge (hT (c t) h (hc t).le)
  let base (t : T) := singletonChain (c t)
  have hstrict (t : T) : RelativeCoverNecessity.StrictLowerChain t.val (base t) := by
    intro x hx
    change x ∈ ({c t} : Finset P) at hx
    simpa only [Finset.mem_singleton.mp hx] using hc t
  let edge (t : T) := adjoinTop t.val (base t) (hstrict t)
  let tipEdge (t : T) := comparablePair (tip t) (edge t)
    (singletonChain_le_adjoinTop t.val (base t) (hstrict t))
  let baseEdge (t : T) := comparablePair (base t) (edge t)
    (le_adjoinTop t.val (base t) (hstrict t))
  let tipFlag (t : T) := singletonChain (tip t)
  let edgeFlag (t : T) := singletonChain (edge t)
  let baseFlag (t : T) := singletonChain (base t)
  let F₀ := glue incl
  let F₁ := glue insertTip
  let F₂ := glue (constantRow tipFlag)
  let F₃ := glue (constantRow tipEdge)
  let F₄ := glue (constantRow edgeFlag)
  let F₅ := glue (constantRow baseEdge)
  let F₆ := glue (constantRow baseFlag)
  have h01 : F₀.val ≤ F₁.val :=
    glue_le (f := incl) (g := insertTip) (fun t s => Finset.subset_insert (tip t) s.val.finset)
  have h21 : F₂.val ≤ F₁.val :=
    glue_le (f := constantRow tipFlag) (g := insertTip)
      (fun _ _ => Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  have h23 : F₂.val ≤ F₃.val :=
    glue_le (f := constantRow tipFlag) (g := constantRow tipEdge)
      (fun _ _ => Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  have h43 : F₄.val ≤ F₃.val :=
    glue_le (f := constantRow edgeFlag) (g := constantRow tipEdge) (fun _ _ =>
      Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have h45 : F₄.val ≤ F₅.val :=
    glue_le (f := constantRow edgeFlag) (g := constantRow baseEdge) (fun _ _ =>
      Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have h65 : F₆.val ≤ F₅.val :=
    glue_le (f := constantRow baseFlag) (g := constantRow baseEdge)
      (fun _ _ => Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  have path : EqvGen (fun a b : FixedOrderMaps A E => a.val ≤ b.val) F₀ F₆ :=
    .trans _ _ _ (.rel _ _ h01) <|
      .trans _ _ _ (.symm _ _ (.rel _ _ h21)) <|
        .trans _ _ _ (.rel _ _ h23) <|
          .trans _ _ _ (.symm _ _ (.rel _ _ h43)) <|
            .trans _ _ _ (.rel _ _ h45) (.symm _ _ (.rel _ _ h65))
  refine ⟨F₆, ?_, ?_⟩
  · rw [← glue_incl]
    exact path
  · intro s
    by_cases hs : s.val ∈ E
    · exact (F₆.property s hs).symm ▸ hs
    · change (glue (constantRow baseFlag)).val s ∈ E
      rw [glue_new _ s hs]
      intro a ha x hx
      change a ∈ ({base (label s hs)} : Finset (NonemptyFiniteChains P)) at ha
      rcases Finset.mem_singleton.mp ha with rfl
      change x ∈ ({c (label s hs)} : Finset P) at hx
      simpa only [Finset.mem_singleton.mp hx] using hc_old (label s hs)

/-- Adjoining any set of maximal elements with strict predecessors gives a
lower two-cover of the second subdivision. Both pieces contain the full old
region and have order fences into it that fix it at every step. -/
theorem exists_relative_two_cover_double_subdivision [Finite P]
    {T : Set P} (hT : ∀ t ∈ T, IsMax t) (hlt : ∀ t : T, ∃ x : P, x < t.val) :
    ∃ A : Fin 2 → Set (NonemptyFiniteChains (NonemptyFiniteChains P)),
      (∀ i, IsLowerSet (A i) ∧ liftedRegion (chainsAvoiding T) ⊆ A i ∧
        RelativeOrderFence (A i) (liftedRegion (chainsAvoiding T))) ∧
      ∀ s, ∃ i, s ∈ A i := by
  classical
  let V₀ := liftedRegion (meetsOld T)
  let V₁ := maximaSide T
  let E := liftedRegion (chainsAvoiding T)
  have old₀ : E ⊆ V₀ := by
    intro s hs a ha
    obtain ⟨x, hx⟩ := a.nonempty
    exact ⟨x, hx, hs a ha x hx⟩
  have old₁ : E ⊆ V₁ := fun _ hs => Or.inl hs
  have lower₁ : IsLowerSet V₁ := by
    intro s u hus hs
    rcases hs with hs | ⟨t, ht⟩
    · exact Or.inl (liftedRegion_lower (chainsAvoiding T) hus hs)
    · exact Or.inr ⟨t, liftedRegion_lower {a : NonemptyFiniteChains P | t.val ∈ a.finset} hus ht⟩
  let A (i : Fin 2) := if i = 0 then V₀ else V₁
  refine ⟨A, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · simpa only [A, ite_eq_left hi] using
        And.intro (liftedRegion_lower (meetsOld T)) (And.intro old₀ (meeting_flags_fence T))
    · simpa only [A, ite_eq_right hi] using
        And.intro lower₁ (And.intro old₁ (maxima_flags_fence hT hlt))
  · intro s
    by_cases hs : s ∈ V₀
    · exact ⟨0, by simpa only [A, ite_eq_left (rfl : (0 : Fin 2) = 0)] using hs⟩
    have bad : ∃ a ∈ s.finset, a ∉ meetsOld T := by
      by_contra hn
      apply hs
      intro a ha
      by_contra hna
      exact hn ⟨a, ha, hna⟩
    obtain ⟨a, ha, haOld⟩ := bad
    have selected (x : P) (hx : x ∈ a.finset) : x ∈ T := by
      by_contra h
      exact haOld ⟨x, hx, h⟩
    obtain ⟨t, ht⟩ := a.nonempty
    let top : T := ⟨t, selected t ht⟩
    have ha_single : a ≤ singletonChain t := by
      intro x hx
      have eq : (⟨x, selected x hx⟩ : T) = top :=
        eq_of_selected_mem hT a ⟨x, selected x hx⟩ top hx ht
      exact Finset.mem_singleton.mpr (congrArg Subtype.val eq)
    have all_contain : s ∈ flagsContaining top.val := by
      intro b hb
      rcases s.comparable ⟨a, ha⟩ ⟨b, hb⟩ with hab | hba
      · change a ≤ b at hab
        exact hab ht
      · change b ≤ a at hba
        exact isMin_singletonChain t (hba.trans ha_single) (Finset.mem_singleton_self t)
    have h₁ : s ∈ V₁ := Or.inr ⟨top, all_contain⟩
    have hne : (1 : Fin 2) ≠ 0 := by decide
    exact ⟨1, by simpa only [A, ite_eq_right hne] using h₁⟩

section Categorical

open private categorical_of_meeting map_fence from D5.S3.Topology.SubdivisionCategoricalCover

/-- A categorical old inclusion yields a categorical lower two-cover at
depth two. The contractions append the lifted old contraction to the
relative fences. -/
theorem hasCategoricalCover_double_subdivision [Finite P]
    {T : Set P} (hT : ∀ t ∈ T, IsMax t) (hlt : ∀ t : T, ∃ x : P, x < t.val)
    (hOld : Categorical (Tᶜ : Set P)) :
    HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains P)) 2 := by
  classical
  let := Fintype.ofFinite P
  let : Finite (NonemptyFiniteChains P) :=
    Finite.of_injective (fun a : NonemptyFiniteChains P => a.finset)
      (fun _ _ h => NonemptyFiniteChains.ext h)
  let E := liftedRegion (chainsAvoiding T)
  -- Each use of categorical_of_meeting lifts the old fence by one subdivision.
  have hchains : Categorical (chainsAvoiding T) := by
    apply categorical_of_meeting hOld
    intro a
    obtain ⟨x, hx⟩ := a.val.nonempty
    exact ⟨x, hx, a.property x hx⟩
  have hflags : Categorical E := by
    apply categorical_of_meeting hchains
    intro s
    obtain ⟨a, ha⟩ := s.val.nonempty
    exact ⟨a, ha, s.property a ha⟩
  obtain ⟨A, hA, cover⟩ := exists_relative_two_cover_double_subdivision hT hlt
  obtain ⟨c, hc⟩ := hflags
  refine ⟨A, ?_, cover⟩
  intro i
  obtain ⟨last, path, hlast⟩ := (hA i).2.2
  let r : A i →o E := ⟨fun s => ⟨last.val s, hlast s⟩, fun _ _ h => last.val.monotone h⟩
  have first : EqvGen (· ≤ ·) (OrderEmbedding.subtype (A i)).toOrderHom last.val :=
    map_fence (fun f : FixedOrderMaps (A i) E => f.val)
      (fun _ _ h => .rel _ _ h) path
  have rest : EqvGen (· ≤ ·) last.val (OrderHom.const (A i) c) :=
    map_fence (fun f : E →o Flag P => f.comp r)
      (fun _ _ h => .rel _ _ (fun s => OrderHom.le_def.mp h (r s))) hc
  exact ⟨(hA i).1, c, .trans _ _ _ first rest⟩

end Categorical

end D5.S3.Topology.StableCategory.RelativeMaximaDoubleSubdivision
