/- GID: D5/S3/ConceptDynamics/PartialIdentification/RelativePastWordRecovery
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/RelativePastWordRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary preloads admit exact relative-past recovery of finite event words. -/

module

public import D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

/-! Label recovery for finite executions from arbitrary preloaded event sets. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery

open EnabledPathSwapConnectivity
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

universe u v

variable {E : Type u} [PartialOrder E] {A : Type v}

/-- Executing an induced residual set lifts to the original order with the preload retained. -/
private theorem exec_relative_lift (I S : Set E)
    (hfresh : ∀ x ∈ S, x ∉ I)
    (hclosed : ∀ x ∈ S, ∀ d, d < x → d ∈ I ∨ d ∈ S)
    {K L : Set S} {l : List S} (hl : Exec K l L) :
    Exec (I ∪ Subtype.val '' K) (l.map Subtype.val) (I ∪ Subtype.val '' L) := by
  induction l generalizing K with
  | nil => cases hl; rfl
  | cons a t ih =>
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rintro (haI | ⟨x, hx, hxa⟩)
        · exact hfresh a a.property haI
        · exact hl.1.1 ((Subtype.ext hxa) ▸ hx)
      · intro d hd
        rcases hclosed a a.property d hd with hdI | hdS
        · exact Or.inl hdI
        · exact Or.inr ⟨⟨d, hdS⟩, hl.1.2 ⟨d, hdS⟩ hd, rfl⟩
    · simpa only [Set.image_insert_eq, Set.union_insert] using ih hl.2

/-- A finite residual set closed under missing predecessors can actually be executed. -/
private theorem finite_relative_exec (I S : Set E) (hfin : S.Finite)
    (hfresh : ∀ x ∈ S, x ∉ I)
    (hclosed : ∀ x ∈ S, ∀ d, d < x → d ∈ I ∨ d ∈ S) :
    ∃ l : List E, Exec I l (I ∪ S) := by
  classical
  let : Fintype S := hfin.fintype
  obtain ⟨l, hl⟩ := (EnabledPathSwapConnectivity.result (∅ : Set S) Set.univ
    (by simp [IsLowerSet]) (by simp [IsLowerSet]) (Set.empty_subset _)).2.1
  refine ⟨l.map Subtype.val, ?_⟩
  have h := exec_relative_lift I S hfresh hclosed hl
  have himage : Subtype.val '' (Set.univ : Set S) = S := by ext x; simp
  simpa only [Set.image_empty, Set.union_empty, himage] using h

/-- Every strict predecessor missing from the preload occurs in the finite word. -/
private theorem exec_past_mem {I J : Set E} {l : List E} (hl : Exec I l J) :
    ∀ e ∈ l, ∀ d, d < e → d ∈ I ∨ d ∈ l := by
  induction l generalizing I with
  | nil => simp
  | cons a t ih =>
    intro e he d hd
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inl (hl.1.2 d hd)
    · rcases ih hl.2 e he d hd with hdI | hdt
      · rcases hdI with rfl | hdI
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl hdI
      · exact Or.inr (List.mem_cons_of_mem _ hdt)

/-- Comparable equally labelled heads of two actual executions must be the same event. -/
private theorem recover_exec (label : E → A) {I J K : Set E} {l m : List E}
    (hl : Exec I l J) (hm : Exec I m K)
    (hc : ∀ a ∈ l, ∀ b ∈ m, label a = label b → a ≤ b ∨ b ≤ a)
    (hw : l.map label = m.map label) : l = m := by
  induction l generalizing I m with
  | nil =>
    cases m with
    | nil => rfl
    | cons b s => simp at hw
  | cons a t ih =>
    cases m with
    | nil => simp at hw
    | cons b s =>
      have heq : a = b := by
        by_contra hne
        rcases hc a (List.mem_cons_self ..) b (List.mem_cons_self ..)
          (List.cons.inj hw).1 with hab | hba
        · exact hl.1.1 (hm.1.2 a (lt_of_le_of_ne hab hne))
        · exact hm.1.1 (hl.1.2 b (lt_of_le_of_ne hba (Ne.symm hne)))
      subst b
      congr 1
      exact ih hl.2 hm.2
        (fun x hx y hy => hc x (List.mem_cons_of_mem _ hx) y
          (List.mem_cons_of_mem _ hy)) (List.cons.inj hw).2

/-- Two incomparable fresh events with finite residual past have a common actual enabling prefix. -/
private theorem common_enabled_prefix (I : Set E) (a b : E)
    (ha : a ∉ I) (hb : b ∉ I)
    (hfa : (Set.Iio a \ I).Finite) (hfb : (Set.Iio b \ I).Finite)
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    ∃ (p : List E) (K : Set E), Exec I p K ∧ Enabled K a ∧ Enabled K b := by
  classical
  let S : Set E := (Set.Iio a \ I) ∪ (Set.Iio b \ I)
  have hfresh : ∀ x ∈ S, x ∉ I := fun x hx => hx.elim And.right And.right
  have hclosed : ∀ x ∈ S, ∀ d, d < x → d ∈ I ∨ d ∈ S := by
    intro x hx d hd
    by_cases hdI : d ∈ I
    · exact Or.inl hdI
    · right
      rcases hx with hx | hx
      · exact Or.inl ⟨hd.trans hx.1, hdI⟩
      · exact Or.inr ⟨hd.trans hx.1, hdI⟩
  obtain ⟨p, hp⟩ := finite_relative_exec I S (hfa.union hfb) hfresh hclosed
  refine ⟨p, I ∪ S, hp, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro (haI | haS)
    · exact ha haI
    · rcases haS with haS | haS
      · exact lt_irrefl a haS.1
      · exact hab haS.1.le
  · intro d hd
    by_cases hdI : d ∈ I
    · exact Or.inl hdI
    · exact Or.inr (Or.inl ⟨hd, hdI⟩)
  · rintro (hbI | hbS)
    · exact hb hbI
    · rcases hbS with hbS | hbS
      · exact hba hbS.1.le
      · exact lt_irrefl b hbS.1
  · intro d hd
    by_cases hdI : d ∈ I
    · exact Or.inl hdI
    · exact Or.inr (Or.inr ⟨hd, hdI⟩)

/-- Label words identify all finite locally legal event words exactly when equally labelled
fresh events with finite strict past outside the arbitrary preload are comparable. -/
theorem result (I : Set E) (label : E → A) :
    Function.Injective (fun l : {l : List E // ∃ J : Set E, Exec I l J} => l.val.map label) ↔
      ∀ a b : E, a ∉ I → b ∉ I →
        (Set.Iio a \ I).Finite → (Set.Iio b \ I).Finite →
        label a = label b → a ≤ b ∨ b ≤ a := by
  classical
  constructor
  · intro hinj a b ha hb hfa hfb hlabel
    by_contra hcomp
    have hab : ¬ a ≤ b := fun h => hcomp (Or.inl h)
    have hba : ¬ b ≤ a := fun h => hcomp (Or.inr h)
    obtain ⟨p, K, hp, hea, heb⟩ := common_enabled_prefix I a b ha hb hfa hfb hab hba
    let x : {l : List E // ∃ J : Set E, Exec I l J} :=
      ⟨p ++ [a], insert a K, exec_append hp ⟨hea, rfl⟩⟩
    let y : {l : List E // ∃ J : Set E, Exec I l J} :=
      ⟨p ++ [b], insert b K, exec_append hp ⟨heb, rfl⟩⟩
    have hwords : x.val.map label = y.val.map label := by
      simp only [x, y, List.map_append, List.map_cons, List.map_nil, hlabel]
    have heq : p ++ [a] = p ++ [b] := congrArg Subtype.val (hinj hwords)
    have heq' : a = b := (List.cons.inj (List.append_cancel_left heq)).1
    exact hab (le_of_eq heq')
  · intro hc x y hwords
    apply Subtype.ext
    obtain ⟨J, hx⟩ := x.property
    obtain ⟨K, hy⟩ := y.property
    apply recover_exec label hx hy (fun a ha b hb hab => ?_) hwords
    have haf : (Set.Iio a \ I).Finite := x.val.finite_toSet.subset (by
      intro d hd
      exact (exec_past_mem hx a ha d hd.1).resolve_left hd.2)
    have hbf : (Set.Iio b \ I).Finite := y.val.finite_toSet.subset (by
      intro d hd
      exact (exec_past_mem hy b hb d hd.1).resolve_left hd.2)
    exact hc a b (((exec_data hx).2.2 a).mp ha).2
      (((exec_data hy).2.2 b).mp hb).2 haf hbf hab

end D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery
