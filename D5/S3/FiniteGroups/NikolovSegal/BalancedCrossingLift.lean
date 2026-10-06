/- GID: D5/S3/FiniteGroups/NikolovSegal/BalancedCrossingLift
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/BalancedCrossingLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.BalancedCrossing

set_option autoImplicit false

open scoped List

namespace NikolovSegal.BalancedCrossing
universe u
variable {V : Type u} [DecidableEq V]

/-- Split a sublist at its first retained letter, including every skipped letter. -/
theorem sublist_cons_split {a : V} {L W : List V} (h : a::L <+ W) :
    ∃ A B, W = A ++ a::B ∧ L <+ B := by
  induction W with
  | nil => simp at h
  | cons b W ih =>
    rcases List.sublist_cons_iff.mp h with htail | ⟨R,he,hR⟩
    · obtain ⟨A,B,hW,hL⟩ := ih htail
      exact ⟨b::A,B,by simp [hW],hL⟩
    · cases he
      exact ⟨[],_,rfl,hR⟩

theorem crossing_core {W : Word V} (h : Crossing W) :
    ∃ (x y : V) (sx sy : Bool), x ≠ y ∧
      [(x,!sx),(y,!sy),(x,sx),(y,sy)] <+ W := by
  obtain ⟨x,y,sx,sy,A,B,C,D,E,hxy,hW⟩ := h
  refine ⟨x,y,sx,sy,hxy,?_⟩
  have h4 := (List.Sublist.cons_cons (y,sy) (List.nil_sublist E)).trans
    (List.sublist_append_right D _)
  have h3 := (List.Sublist.cons_cons (x,sx) h4).trans
    (List.sublist_append_right C _)
  have h2 := (List.Sublist.cons_cons (y,!sy) h3).trans
    (List.sublist_append_right B _)
  have h1 := (List.Sublist.cons_cons (x,!sx) h2).trans
    (List.sublist_append_right A _)
  simpa [hW,List.append_assoc] using h1

theorem crossing_of_core {W : Word V} (x y : V) (sx sy : Bool) (hxy : x ≠ y)
    (h : [(x,!sx),(y,!sy),(x,sx),(y,sy)] <+ W) : Crossing W := by
  obtain ⟨A,W1,hW,h1⟩ := sublist_cons_split h
  obtain ⟨B,W2,hW1,h2⟩ := sublist_cons_split h1
  obtain ⟨C,W3,hW2,h3⟩ := sublist_cons_split h2
  obtain ⟨D,E,hW3,_⟩ := sublist_cons_split h3
  refine ⟨x,y,sx,sy,A,B,C,D,E,hxy,?_⟩
  simp [hW,hW1,hW2,hW3,List.append_assoc]

theorem crossing_sublist {W R : Word V} (h : Crossing R) (hs : R <+ W) : Crossing W := by
  obtain ⟨x,y,sx,sy,hxy,hc⟩ := crossing_core h
  exact crossing_of_core x y sx sy hxy (hc.trans hs)

/-- Literal Lemma 8.1 on the original unreduced word.  Nonidentity will be
established from the exact colour bound in the quantitative module. -/
theorem balanced_nontrivial_crossing {W : Word V} (hb : Balanced W)
    (hne : FreeGroup.mk W ≠ 1) : Crossing W := by
  have hred := FreeGroup.reduce.red (L := W)
  have hbal := balanced_red hb hred
  have hnot : FreeGroup.reduce W ≠ [] := by
    intro he
    apply hne
    have hh := FreeGroup.reduce.self (L := W)
    rw [he] at hh
    exact hh.symm
  exact crossing_sublist
    (reduced_crossing hbal (FreeGroup.isReduced_iff_reduce_eq.mpr FreeGroup.reduce.idem) hnot)
    hred.sublist

/-- Signed balance alone proves that each extracted key is absent from all
five retained segments. -/
theorem crossing_fresh {W : Word V} (hb : Balanced W)
    (x y : V) (sx sy : Bool) (A B C D E : Word V)
    (hW : W = A ++ [(x,!sx)] ++ B ++ [(y,!sy)] ++ C ++ [(x,sx)] ++ D ++ [(y,sy)] ++ E) :
    ∀ p ∈ A++B++C++D++E, p.1 ≠ x ∧ p.1 ≠ y := by
  rintro ⟨z,t⟩ hp
  have hc := List.count_pos_iff.mpr hp
  simp only [List.count_append] at hc
  constructor
  · intro he; change z = _ at he; subst z
    have hle := List.nodup_iff_count_le_one.mp hb.1 (x,t)
    rw [hW] at hle
    cases sx <;> cases t <;> simp [List.count_append,List.count_cons] at hle <;> omega
  · intro he; change z = _ at he; subst z
    have hle := List.nodup_iff_count_le_one.mp hb.1 (y,t)
    rw [hW] at hle
    cases sy <;> cases t <;> simp [List.count_append,List.count_cons] at hle <;> omega

/-- Removing the two crossing pairs and reordering the retained segments
preserves literal signed balance. -/
theorem crossing_balanced {W : Word V} (hb : Balanced W)
    (x y : V) (sx sy : Bool) (A B C D E : Word V)
    (hW : W = A ++ [(x,!sx)] ++ B ++ [(y,!sy)] ++ C ++ [(x,sx)] ++ D ++ [(y,sy)] ++ E) :
    Balanced (A++D++C++B++E) := by
  constructor
  · apply List.nodup_iff_count_le_one.mpr
    intro p
    have hle := List.nodup_iff_count_le_one.mp hb.1 p
    rw [hW] at hle
    simp only [List.count_append,List.count_cons,List.count_nil] at hle ⊢
    omega
  · intro z
    have hc := hb.2 z
    rw [hW] at hc
    cases sx <;> cases sy <;> by_cases hx : z = x <;> by_cases hy : z = y <;>
      simp [List.count_append,List.count_cons,hx,hy] at hc ⊢ <;> omega

theorem crossing_support_card {W : Word V} (hb : Balanced W)
    (x y : V) (sx sy : Bool) (A B C D E : Word V)
    (hW : W = A ++ [(x,!sx)] ++ B ++ [(y,!sy)] ++ C ++ [(x,sx)] ++ D ++ [(y,sy)] ++ E) :
    (support (A++D++C++B++E)).card + 2 = (support W).card := by
  have hR := crossing_balanced hb x y sx sy A B C D E hW
  have hl := balanced_length hb
  have hr := balanced_length hR
  have he : W.length = (A++D++C++B++E).length + 4 := by
    rw [hW]
    simp only [List.length_append,List.length_singleton]
    omega
  omega

end NikolovSegal.BalancedCrossing
