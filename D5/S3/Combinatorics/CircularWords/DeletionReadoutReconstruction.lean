/- GID: D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labeled deletions reconstruct oriented nodup circles on at least four labels. -/

import D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-! Reconstruction uses actual circular deletion residuals and preserves orientation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

open CircularDeletionTransport CyclicInsertionGap
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u
variable {α : Type u} [DecidableEq α]

private theorem mem_support (C : Cycle α) (x : α) : x ∈ C.toFinset ↔ x ∈ C := by
  induction C using Quotient.inductionOn with
  | _ l => exact List.mem_toFinset

omit [DecidableEq α] in
private theorem rooted {C : Cycle α} {r : α} (hr : r ∈ C) :
    ∃ L : List α, C = (r :: L : List α) := by
  induction C using Quotient.inductionOn with
  | _ W =>
    obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp (Cycle.mem_coe_iff.mp hr)
    refine ⟨Q ++ P, Cycle.coe_eq_coe.mpr ⟨P.length, ?_⟩⟩
    simpa only [List.cons_append] using List.rotate_append_length_eq P (r :: Q)

private theorem filter_absent {L : List α} {x : α} (hx : x ∉ L) :
    L.filter (fun y => decide (y ≠ x)) = L := by
  apply List.filter_eq_self.mpr
  intro y hy
  simp only [decide_eq_true_eq]
  exact fun e => hx (e ▸ hy)

/-- Labeled one-label deletions determine a nodup oriented circle on fixed support
of size at least four. Rotation, but not reversal, is identified by `Cycle`. -/
theorem reconstruct {A : Finset α} (hA : 4 ≤ A.card)
    {C D : Cycle α} (hC : C.Nodup) (hD : D.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A)
    (deck : ∀ x ∈ A, delete x C = delete x D) : C = D := by
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  obtain ⟨L, rfl⟩ := rooted ((mem_support C r).mp (by simpa only [sC] using hr))
  obtain ⟨K, rfl⟩ := rooted ((mem_support D r).mp (by simpa only [sD] using hr))
  have hnL := Cycle.nodup_coe_iff.mp hC
  have hnK := Cycle.nodup_coe_iff.mp hD
  have hL0 : L ≠ [] := by
    intro e
    subst L
    have : A.card = 1 := by simpa using congrArg Finset.card sC.symm
    omega
  have hK0 : K ≠ [] := by
    intro e
    subst K
    have : A.card = 1 := by simpa using congrArg Finset.card sD.symm
    omega
  cases L with
  | nil => exact (hL0 rfl).elim
  | cons a L =>
    cases K with
    | nil => exact (hK0 rfl).elim
    | cons b K =>
      have hex : ∃ x ∈ A, x ∉ ({r, a, b} : Finset α) := by
        by_contra h
        have hs : A ⊆ ({r, a, b} : Finset α) := by
          intro x hx
          by_contra hn
          exact h ⟨x, hx, hn⟩
        have hc := Finset.card_le_card hs
        have ht : ({r, a, b} : Finset α).card ≤ 3 := Finset.card_le_three
        omega
      obtain ⟨x, hxA, hx⟩ := hex
      have hxr : r ≠ x := by
        intro e
        apply hx
        simp [e]
      have hxa : a ≠ x := by
        intro e
        apply hx
        simp [e]
      have hxb : b ≠ x := by
        intro e
        apply hx
        simp [e]
      have he := deck x hxA
      change (((r :: a :: L).filter (fun y => decide (y ≠ x))) : Cycle α) =
        (((r :: b :: K).filter (fun y => decide (y ≠ x))) : Cycle α) at he
      simp only [List.filter_cons, decide_eq_true hxr, decide_eq_true hxa,
        decide_eq_true hxb, ↓reduceIte] at he
      have hnfiltered : (r :: a :: L.filter (fun y => decide (y ≠ x))).Nodup := by
        simpa only [List.filter_cons, decide_eq_true hxr, decide_eq_true hxa,
          ↓reduceIte] using
          hnL.filter (fun y => decide (y ≠ x))
      have heads := anchored_coe_injective hnfiltered he
      have hab : a = b := (List.cons.inj heads).1
      subst b
      have haA : a ∈ A := sC ▸ (mem_support _ a).mpr (by simp)
      have hra : r ≠ a := by
        intro e
        exact (List.nodup_cons.mp hnL).1 (by simp [e])
      have haL : a ∉ L := (List.nodup_cons.mp (List.nodup_cons.mp hnL).2).1
      have haK : a ∉ K := (List.nodup_cons.mp (List.nodup_cons.mp hnK).2).1
      have tails := deck a haA
      change (((r :: a :: L).filter (fun y => decide (y ≠ a))) : Cycle α) =
        (((r :: a :: K).filter (fun y => decide (y ≠ a))) : Cycle α) at tails
      simp only [List.filter_cons, decide_eq_true_eq, hra, ↓reduceIte, ne_eq,
        not_true_eq_false, decide_false, Bool.false_eq_true, filter_absent haL,
        filter_absent haK] at tails
      have hLK : L = K := anchored_coe_injective
        (List.nodup_cons.mpr ⟨fun h => (List.nodup_cons.mp hnL).1 (by simp [h]),
          (List.nodup_cons.mp (List.nodup_cons.mp hnL).2).2⟩) tails
      rw [hLK]

/-- Actual oriented circles with exactly the prescribed finite support. -/
abbrev SupportedCircle (A : Finset α) := {C : Cycle α // C.Nodup ∧ C.toFinset = A}

/-- The individual readout records the actual oriented residual and its deleted label. -/
def deletionReadout (A : Finset α) (x : A) (C : SupportedCircle A) : Cycle α :=
  delete x.1 C.1

/-- Three labels do not suffice: the two orientations have identical labeled deletions. -/
private theorem three_label_obstruction (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ([a,b,c] : Cycle α) ≠ ([a,c,b] : Cycle α) ∧
    ∀ x ∈ ({a,b,c} : Finset α),
      delete x ([a,b,c] : Cycle α) = delete x ([a,c,b] : Cycle α) := by
  constructor
  · intro h
    have := anchored_coe_injective (by simp [hab,hac,hbc]) h
    exact hbc (List.cons.inj this).1
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · subst x
      change ((([a,b,c] : List α).filter (fun y => decide (y ≠ a))) : Cycle α) =
        ((([a,c,b] : List α).filter (fun y => decide (y ≠ a))) : Cycle α)
      simp only [List.filter_cons, List.filter_nil, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, Ne.symm hab, Ne.symm hac]
      exact Cycle.coe_eq_coe.mpr ⟨1, by simp [List.rotate_cons_succ]⟩
    · subst x
      change ((([a,b,c] : List α).filter (fun y => decide (y ≠ b))) : Cycle α) =
        ((([a,c,b] : List α).filter (fun y => decide (y ≠ b))) : Cycle α)
      simp [hab, Ne.symm hbc]
    · subst x
      change ((([a,b,c] : List α).filter (fun y => decide (y ≠ c))) : Cycle α) =
        ((([a,c,b] : List α).filter (fun y => decide (y ≠ c))) : Cycle α)
      simp [hac, hbc]

/-- Among supports with at least three labels, the actual deletion observations have
diagonal joint kernel exactly when there are at least four labels. -/
theorem deletion_joint_kernel_iff (A : Finset α) (hA : 3 ≤ A.card) :
    jointKernel (deletionReadout A) = diagonal (SupportedCircle A) ↔ 4 ≤ A.card := by
  constructor
  · intro faithful
    by_contra hn
    have hthree : A.card = 3 := by omega
    obtain ⟨a,b,c,hab,hac,hbc,hset⟩ := Finset.card_eq_three.mp hthree
    let C : SupportedCircle A := ⟨([a,b,c] : Cycle α),
      by simp [hab,hac,hbc], by simp [hset]⟩
    let D : SupportedCircle A := ⟨([a,c,b] : Cycle α),
      by simp [hab,hac,hbc.symm], by simp [hset, Finset.pair_comm]⟩
    have boundary := three_label_obstruction a b c hab hac hbc
    have indistinguishable : ∀ x : A, deletionReadout A x C = deletionReadout A x D := by
      intro x
      exact boundary.2 x.1 (hset ▸ x.2)
    have separates := ((joint_faithfulness_tfae (deletionReadout A)).out 3 2).mp faithful
    have he := congrArg Subtype.val (separates C D indistinguishable)
    exact boundary.1 he
  · intro four
    apply ((joint_faithfulness_tfae (deletionReadout A)).out 2 3).mp
    intro C D hd
    apply Subtype.ext
    exact reconstruct four C.2.1 D.2.1 C.2.2 D.2.2
      (fun x hx => hd ⟨x, hx⟩)

#print axioms reconstruct
#print axioms SupportedCircle
#print axioms deletionReadout
#print axioms deletion_joint_kernel_iff
#print axioms three_label_obstruction

end D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
