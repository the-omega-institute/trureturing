/- GID: D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete label histories recover finite induced-poset extensions exactly for chain fibers. -/

import D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery

open EnabledPathSwapConnectivity

universe u v

variable {E : Type u} [PartialOrder E] {A : Type v}

private theorem recover (label : E → A) (l m : List E)
    (hl : l.Pairwise (fun a b => ¬ b ≤ a))
    (hm : m.Pairwise (fun a b => ¬ b ≤ a)) (hp : l.Perm m)
    (hc : ∀ a ∈ l, ∀ b ∈ l, label a = label b → a ≤ b ∨ b ≤ a)
    (hw : l.map label = m.map label) : l = m := by
  induction l generalizing m with
  | nil => exact (List.perm_nil.mp hp.symm).symm
  | cons a t ih =>
    cases m with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at hw
    | cons b s =>
      have hablabel : label a = label b := (List.cons.inj hw).1
      have hb : b ∈ a :: t := hp.mem_iff.mpr (List.mem_cons_self ..)
      have ha : a ∈ b :: s := hp.mem_iff.mp (List.mem_cons_self ..)
      have hab : a = b := by
        by_contra hne
        have hbt : b ∈ t := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
        have has : a ∈ s := (List.mem_cons.mp ha).resolve_left hne
        rcases hc a (List.mem_cons_self ..) b hb hablabel with h | h
        · exact (List.pairwise_cons.mp hm).1 a has h
        · exact (List.pairwise_cons.mp hl).1 b hbt h
      subst b
      congr 1
      exact ih s (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp hm).2
        (List.perm_cons.mp hp)
        (fun x hx y hy => hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        (List.cons.inj hw).2

private theorem extension_map_iff (F : Finset E) (l : List {e // e ∈ F}) :
    ExtensionList (∅ : Set {e // e ∈ F}) Set.univ l ↔
      ExtensionList (∅ : Set E) (F : Set E) (l.map Subtype.val) := by
  classical
  simp only [ExtensionList, Set.mem_empty_iff_false, not_false_eq_true, and_true,
    Set.mem_univ, iff_true]
  constructor
  · rintro ⟨hn, he, hp⟩
    refine ⟨hn.map Subtype.val_injective, ?_, ?_⟩
    · intro e
      constructor
      · intro h
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
        exact x.property
      · intro h
        exact List.mem_map.mpr ⟨⟨e, h⟩, he _, rfl⟩
    · exact List.pairwise_map.mpr hp
  · rintro ⟨hn, he, hp⟩
    refine ⟨List.Nodup.of_map hn, ?_, List.pairwise_map.mp hp⟩
    intro e
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp ((he e.val).mpr e.property)
    exact (Subtype.ext hxe) ▸ hx

private theorem lift_extension (F : Finset E) (l : List E)
    (hl : ExtensionList (∅ : Set E) (F : Set E) l) :
    ∃ t : List {e // e ∈ F},
      ExtensionList (∅ : Set {e // e ∈ F}) Set.univ t ∧ t.map Subtype.val = l := by
  let t : List {e // e ∈ F} := l.attach.map fun x => ⟨x.val, ((hl.2.1 x.val).mp x.property).1⟩
  have ht : t.map Subtype.val = l := by simp [t, List.map_map]
  exact ⟨t, (extension_map_iff F t).mpr (ht.symm ▸ hl), ht⟩

private theorem extension_append {I K J : Set E} (hK : IsLowerSet K)
    (hIK : I ⊆ K) (hKJ : K ⊆ J) {p q : List E}
    (hp : ExtensionList I K p) (hq : ExtensionList K J q) :
    ExtensionList I J (p ++ q) := by
  refine ⟨List.nodup_append.mpr ⟨hp.1, hq.1, ?_⟩, ?_, ?_⟩
  · exact List.disjoint_left.mpr fun x hx hy => ((hq.2.1 x).mp hy).2 ((hp.2.1 x).mp hx).1
  · intro x
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hxK, hxI⟩ := (hp.2.1 x).mp hx
        exact ⟨hKJ hxK, hxI⟩
      · obtain ⟨hxJ, hxK⟩ := (hq.2.1 x).mp hx
        exact ⟨hxJ, fun hxI => hxK (hIK hxI)⟩
    · rintro ⟨hxJ, hxI⟩
      by_cases hxK : x ∈ K
      · exact List.mem_append_left _ ((hp.2.1 x).mpr ⟨hxK, hxI⟩)
      · exact List.mem_append_right _ ((hq.2.1 x).mpr ⟨hxJ, hxK⟩)
  · exact List.pairwise_append.mpr ⟨hp.2.2, hq.2.2, fun x hx y hy h =>
      ((hq.2.1 y).mp hy).2 (hK h ((hp.2.1 x).mp hx).1)⟩

private theorem incomparable_collision [Finite E] (a b : E)
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    ∃ p s : List E,
      ExtensionList (∅ : Set E) Set.univ (p ++ a :: b :: s) ∧
      ExtensionList (∅ : Set E) Set.univ (p ++ b :: a :: s) := by
  classical
  let K : Set E := {x | x < a ∨ x < b}
  have hK : IsLowerSet K := by
    intro x y hyx hx
    exact hx.elim (fun h => Or.inl (lt_of_le_of_lt hyx h))
      (fun h => Or.inr (lt_of_le_of_lt hyx h))
  have ha : a ∉ K := by
    rintro (h | h)
    · exact lt_irrefl _ h
    · exact hab h.le
  have hb : b ∉ K := by
    rintro (h | h)
    · exact hba h.le
    · exact lt_irrefl _ h
  have insert_lower : ∀ x ∈ ({a, b} : Set E), IsLowerSet (insert x K) := by
    intro x hx y z hzy hy
    rcases hy with rfl | hy
    · by_cases hzx : z = x
      · exact Or.inl hzx
      · right
        rcases hx with rfl | hx
        · exact Or.inl (lt_of_le_of_ne hzy hzx)
        · have hxb : x = b := by simpa using hx
          subst x
          exact Or.inr (lt_of_le_of_ne hzy hzx)
    · exact Or.inr (hK hzy hy)
  have hKab : IsLowerSet (insert a (insert b K)) := by
    intro x y hyx hx
    rcases hx with rfl | hx
    · by_cases hya : y = a
      · exact Or.inl hya
      · exact Or.inr (Or.inr (Or.inl (lt_of_le_of_ne hyx hya)))
    · exact Or.inr (insert_lower b (by simp) hyx hx)
  obtain ⟨p, hp⟩ := (EnabledPathSwapConnectivity.result (∅ : Set E) K
    (by simp [IsLowerSet]) hK (Set.empty_subset _)).2.1
  have hpe := (EnabledPathSwapConnectivity.result (∅ : Set E) K
    (by simp [IsLowerSet]) hK (Set.empty_subset _)).1 p |>.mp hp
  obtain ⟨s, hs⟩ := (EnabledPathSwapConnectivity.result (insert a (insert b K)) Set.univ
    hKab (by simp [IsLowerSet]) (Set.subset_univ _)).2.1
  have hse := (EnabledPathSwapConnectivity.result (insert a (insert b K)) Set.univ
    hKab (by simp [IsLowerSet]) (Set.subset_univ _)).1 s |>.mp hs
  have habne : a ≠ b := fun h => hab (h ▸ le_rfl)
  have pair_ab : ExtensionList K (insert a (insert b K)) [a, b] := by
    refine ⟨by simp [habne], ?_, by simp [hba]⟩
    intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, ha⟩
      · exact ⟨Or.inr (Or.inl rfl), hb⟩
    · rintro ⟨hx, hxK⟩
      exact hx.elim Or.inl (fun h => h.elim Or.inr (fun h => (hxK h).elim))
  have pair_ba : ExtensionList K (insert a (insert b K)) [b, a] := by
    refine ⟨by simp [habne], ?_, by simp [hab]⟩
    intro x
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_comm] using pair_ab.2.1 x
  have hsub : K ⊆ insert a (insert b K) := fun _ h => Or.inr (Or.inr h)
  have left := extension_append hK (Set.empty_subset _) hsub hpe pair_ab
  have right := extension_append hK (Set.empty_subset _) hsub hpe pair_ba
  refine ⟨p, s, ?_, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      extension_append hKab (Set.empty_subset _) (Set.subset_univ _) left hse
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      extension_append hKab (Set.empty_subset _) (Set.subset_univ _) right hse

/-- Label observation distinguishes all complete induced-order extensions exactly
when every equal-label fiber in the finite support is a chain. -/
theorem result (F : Finset E) (label : E → A) :
    (∀ a ∈ F, ∀ b ∈ F, label a = label b → a ≤ b ∨ b ≤ a) ↔
    (∀ l m : List E,
      ExtensionList (∅ : Set E) (F : Set E) l →
      ExtensionList (∅ : Set E) (F : Set E) m →
      l.map label = m.map label → l = m) := by
  classical
  constructor
  · intro hc l m hl hm hw
    obtain ⟨t, ht, htl⟩ := lift_extension F l hl
    obtain ⟨s, hs, hsm⟩ := lift_extension F m hm
    have hp : t.Perm s := (List.perm_ext_iff_of_nodup ht.1 hs.1).mpr
      (fun e => (ht.2.1 e).trans (hs.2.1 e).symm)
    have hts : t = s := recover (fun e => label e.val) t s ht.2.2 hs.2.2 hp
      (fun a _ b _ => hc a.val a.property b.val b.property)
      (by simpa only [← htl, ← hsm, List.map_map] using hw)
    exact htl.symm.trans ((congrArg (List.map Subtype.val) hts).trans hsm)
  · intro hi a ha b hb hablabel
    by_contra hc
    have hab : ¬ a ≤ b := fun h => hc (Or.inl h)
    have hba : ¬ b ≤ a := fun h => hc (Or.inr h)
    let x : {e // e ∈ F} := ⟨a, ha⟩
    let y : {e // e ∈ F} := ⟨b, hb⟩
    obtain ⟨p, s, hl, hm⟩ := incomparable_collision x y hab hba
    have heq := hi _ _ ((extension_map_iff F _).mp hl)
      ((extension_map_iff F _).mp hm) (by simp [List.map_map, hablabel, x, y])
    have eqsub : p ++ x :: y :: s = p ++ y :: x :: s :=
      (List.map_injective_iff.mpr Subtype.val_injective) heq
    have hxy : x = y := (List.cons.inj (List.append_cancel_left eqsub)).1
    exact hab (le_of_eq (congrArg Subtype.val hxy))

#print axioms result

end D5.S3.ConceptDynamics.PartialIdentification.LabelledExtensionRecovery
