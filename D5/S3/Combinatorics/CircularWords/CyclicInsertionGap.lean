/- GID: D5/S3/Combinatorics/CircularWords/CyclicInsertionGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/CyclicInsertionGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Every oriented one-label insertion has a unique actual cyclic gap. -/

import D5.S3.Combinatorics.CircularWords.CircularDeletionTransport

set_option autoImplicit false
namespace D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
universe u
variable {α : Type u} [DecidableEq α]

/-- An actual oriented circular word with a new label in one gap. -/
def gapCircle (B : List α) (x : α) (j : Fin B.length) : Cycle α :=
  (x :: B.rotate j.val : List α)

private theorem anchored_coe_injective {x : α} {L K : List α}
    (hL : (x :: L).Nodup) (h : (x :: L : List α) = (x :: K : Cycle α)) : L = K := by
  obtain ⟨n, hn⟩ := Cycle.coe_eq_coe.mp h
  let j := n % (x :: L).length
  have hj : j < (x :: L).length := Nat.mod_lt _ (by simp)
  have hr : (x :: L).rotate j = x :: K := (List.rotate_mod _ n).trans hn
  have hget : (x :: L)[j] = (x :: L)[0] := by
    have hh := congrArg List.head? hr
    rw [List.head?_rotate hj] at hh
    simpa only [List.getElem?_eq_getElem hj, List.head?_cons,
      List.getElem_cons_zero, Option.some.injEq] using hh
  have hj0 : j = 0 := hL.getElem_inj_iff.mp hget
  simpa only [hj0, List.rotate_zero, List.cons.injEq, true_and] using hr

private theorem gapCircle_nodup {B : List α} {x : α}
    (hB : B.Nodup) (hx : x ∉ B) (j : Fin B.length) : (gapCircle B x j).Nodup := by
  apply Cycle.nodup_coe_iff.mpr
  exact List.nodup_cons.mpr ⟨by simpa using hx, List.nodup_rotate.mpr hB⟩

private theorem gapCircle_delete {B : List α} {x : α}
    (hx : x ∉ B) (j : Fin B.length) : delete x (gapCircle B x j) = (B : Cycle α) := by
  have hf : (B.rotate j.val).filter (fun y => decide (y ≠ x)) = B.rotate j.val := by
    apply List.filter_eq_self.mpr
    intro y hy
    simp only [decide_eq_true_eq]
    intro he
    subst y
    exact hx (List.mem_rotate.mp hy)
  change (((x :: B.rotate j.val).filter (fun y => decide (y ≠ x))) : Cycle α) = _
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte, hf]
  exact Cycle.coe_eq_coe.mpr (List.IsRotated.forall B j.val)

/-- All oriented circular insertions, including every gap, are independently classified. -/
private theorem gapCircle_unique {B : List α} {x : α} (hB : B.Nodup) (hB0 : B ≠ [])
    (hx : x ∉ B) {C : Cycle α} (hC : C.Nodup) (hCx : x ∈ C)
    (hd : delete x C = (B : Cycle α)) :
    ∃! j : Fin B.length, C = gapCircle B x j := by
  have hex : ∃ j : Fin B.length, C = gapCircle B x j := by
    induction C using Quotient.inductionOn with
    | _ W =>
      obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp (Cycle.mem_coe_iff.mp hCx)
      let L := Q ++ P
      have hr : (P ++ x :: Q : List α) = (x :: L : Cycle α) := by
        apply Cycle.coe_eq_coe.mpr
        refine ⟨P.length, ?_⟩
        simpa only [List.cons_append, L] using List.rotate_append_length_eq P (x :: Q)
      have hn : (x :: L).Nodup := Cycle.nodup_coe_iff.mp (hr ▸ hC)
      have hf : L.filter (fun y => decide (y ≠ x)) = L := by
        apply List.filter_eq_self.mpr
        intro y hy
        simp only [decide_eq_true_eq]
        intro he
        subst y
        exact (List.nodup_cons.mp hn).1 hy
      have hd' : (L : Cycle α) = (B : Cycle α) := by
        change delete x ((P ++ x :: Q : List α) : Cycle α) = (B : Cycle α) at hd
        rw [hr] at hd
        change (((x :: L).filter (fun y => decide (y ≠ x))) : Cycle α) = _ at hd
        simpa only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, hf] using hd
      obtain ⟨n, hnrot⟩ := (Cycle.coe_eq_coe.mp hd').symm
      let j : Fin B.length := ⟨n % B.length, Nat.mod_lt _ (List.length_pos_iff.mpr hB0)⟩
      refine ⟨j, ?_⟩
      have hj : B.rotate j.val = L := (List.rotate_mod B n).trans hnrot
      change ((P ++ x :: Q : List α) : Cycle α) = gapCircle B x j
      rw [hr]
      simp only [gapCircle, hj]
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, ?_⟩
  intro k hk
  have he : B.rotate k.val = B.rotate j.val :=
    anchored_coe_injective (Cycle.nodup_coe_iff.mp (gapCircle_nodup hB hx k))
      (hk.symm.trans hj)
  apply Fin.ext
  simpa only [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt j.isLt]
    using hB.rotate_congr hB0 k.val j.val he

/-- The full deletion fiber is exactly the set of all distinct actual insertion gaps. -/
theorem gapCircle_fiber {B : List α} {x : α} (hB : B.Nodup) (hB0 : B ≠ [])
    (hx : x ∉ B) (C : Cycle α) :
    (C.Nodup ∧ x ∈ C ∧ delete x C = (B : Cycle α)) ↔
      ∃! j : Fin B.length, C = gapCircle B x j := by
  constructor
  · rintro ⟨hC, hCx, hd⟩
    exact gapCircle_unique hB hB0 hx hC hCx hd
  · rintro ⟨j, rfl, _⟩
    refine ⟨gapCircle_nodup hB hx j, ?_, gapCircle_delete hx j⟩
    exact Cycle.mem_coe_iff.mpr List.mem_cons_self

end D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
