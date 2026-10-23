/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceMoore
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceMoore
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual repeated-partner replies force five running and five disjoint whole-output halts in three calls. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery (LiteralRow canonicalRow)
open NativeSixSourceCones

universe u v

/-- These tables and Q+H exhaust the accessible mutable control. The output
is a fixed complete row, with no source-dependent decoding argument. -/
structure Controller (Q : Type u) (H : Type v) where
  addr : Q → Address
  next : Q → Reply → Q ⊕ H
  out : H → LiteralRow

/-- A mathematical trace records actual state visits; it is not accessible
workspace. Shared states, repeated visits and cycles have no restriction. -/
inductive Run {Q : Type u} {H : Type v} (M : Controller Q H) (t : Source) :
    Q ⊕ H → List Q → H → Prop
  | halt (h : H) : Run M t (.inr h) [] h
  | read (s : Q) {tr : List Q} {h : H}
      (tail : Run M t (M.next s (readout (M.addr s) t)) tr h) :
      Run M t (.inl s) (s :: tr) h

private theorem run_agree {Q : Type u} {H : Type v} (M : Controller Q H)
    {t t' : Source} {k : Q ⊕ H} {tr : List Q} {h : H}
    (run : Run M t k tr h)
    (agree : ∀ s ∈ tr, readout (M.addr s) t = readout (M.addr s) t') :
    Run M t' k tr h := by
  induction run with
  | halt h => exact .halt h
  | @read s tr h tail ih =>
      apply Run.read s
      rw [← agree s List.mem_cons_self]
      exact ih (fun p hp => agree p (List.mem_cons_of_mem _ hp))

theorem run_terminal {Q : Type u} {H : Type v} (M : Controller Q H)
    {t : Source} {k : Q ⊕ H} {tr tr' : List Q} {h h' : H}
    (a : Run M t k tr h) (b : Run M t k tr' h') : h = h' := by
  induction a generalizing tr' h' with
  | halt h => cases b; rfl
  | read s tail ih => cases b with | read _ tail' => exact ih tail'

private def positive (j : Fin 4) : Fin 6 := ⟨j.val + 2, by omega⟩
private def rightLocation (j : Fin 4) : Fin 5 := ⟨j.val + 1, by omega⟩
private def sameZero (j : Fin 4) : Fin 6 := if j.val < 2 then 0 else 1

private theorem pair_questions (j : Fin 4) (a : Address)
    (avoid : location a ≠ some (rightLocation j)) :
    question a (sameZero j) = question a (positive j) := by
  have finite : ∀ (j : Fin 4) (d : Option (Fin 5)), d ≠ some (rightLocation j) →
      (match d with
       | none => false
       | some k => if k = 0 then groupA (sameZero j) else decide ((sameZero j).val = k.val + 1)) =
      (match d with
       | none => false
       | some k => if k = 0 then groupA (positive j) else decide ((positive j).val = k.val + 1)) := by
    decide +kernel
  exact finite j (location a) avoid

private theorem zero_questions (j : Fin 4) (a : Address)
    (partner : location a ≠ some 0) (avoid : location a ≠ some (rightLocation j)) :
    question a 0 = question a (positive j) := by
  have finite : ∀ (j : Fin 4) (d : Option (Fin 5)),
      d ≠ some 0 → d ≠ some (rightLocation j) →
      (match d with
       | none => false
       | some k => if k = 0 then groupA 0 else decide ((0 : Fin 6).val = k.val + 1)) =
      (match d with
       | none => false
       | some k => if k = 0 then groupA (positive j) else decide ((positive j).val = k.val + 1)) := by
    decide +kernel
  exact finite j (location a) partner avoid

private theorem reply_of_question (a : Address) (z z' : Fin 6)
    (h : question a z = question a z') : readout a (current z) = readout a (current z') := by
  obtain ⟨f,hf⟩ := all_address_factor a
  rw [hf,hf,h]

/-- Every successful finite stationary controller on the entire original
infinite fiber, with one common entry and at most three actual calls, has at
least five running states and five halts. All unused states are counted. -/
theorem three_call_state_obstruction {Q : Type u} {H : Type v}
    [Fintype Q] [Fintype H] (M : Controller Q H) (entry : Q ⊕ H)
    (correct : ∀ x : Fiber, ∃ h tr,
      Run M (substitution x.val) entry tr h ∧
      M.out h = canonicalRow P x.val ∧ tr.length ≤ 3) :
    5 ≤ Fintype.card Q ∧ 5 ≤ Fintype.card H ∧ 10 ≤ Fintype.card (Q ⊕ H) := by
  classical
  have six (z : Fin 6) : ∃ h tr, Run M (current z) entry tr h ∧
      M.out h = predecessor (label z) ∧ tr.length ≤ 3 := by
    obtain ⟨h,tr,run,out,budget⟩ := correct (actual z)
    refine ⟨h,tr,?_,?_,budget⟩
    · simpa only [actual, (six_source_realization.1 z).1] using run
    · exact out.trans (six_source_realization.1 z).2.2
  choose h tr runs outputs budgets using six
  have distinguish (z z' : Fin 6) (ne : label z ≠ label z') :
      ∃ s ∈ tr z, question (M.addr s) z ≠ question (M.addr s) z' := by
    by_contra missing
    push_neg at missing
    have run' := run_agree M (runs z) (fun s hs => reply_of_question _ _ _ (missing s hs))
    have halt := run_terminal M run' (runs z')
    exact ne (six_source_realization.2 ((outputs z).symm.trans
      ((congrArg M.out halt).trans (outputs z'))))
  have rights (j : Fin 4) : ∃ s : Q, location (M.addr s) = some (rightLocation j) := by
    have ne : label (sameZero j) ≠ label (positive j) := by
      revert j; decide +kernel
    obtain ⟨s,_,hs⟩ := distinguish (sameZero j) (positive j) ne
    exact ⟨s, Classical.byContradiction (fun hn => hs (pair_questions j _ hn))⟩
  have partner : ∃ s : Q, location (M.addr s) = some 0 := by
    by_contra absent
    push_neg at absent
    have visits (j : Fin 4) : ∃ s ∈ tr 0, location (M.addr s) = some (rightLocation j) := by
      have ne : label 0 ≠ label (positive j) := by revert j; decide +kernel
      obtain ⟨s,hs,neq⟩ := distinguish 0 (positive j) ne
      exact ⟨s,hs,Classical.byContradiction (fun hn => neq (zero_questions j _ (absent s) hn))⟩
    have inj : Function.Injective (fun j : Fin 4 => some (rightLocation j)) := by
      decide +kernel
    have sub : Finset.univ.image (fun j : Fin 4 => some (rightLocation j)) ⊆
        (tr 0).toFinset.image (fun s => location (M.addr s)) := by
      intro d hd
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨s,hs,eq⟩ := visits j
      exact Finset.mem_image.mpr ⟨s,List.mem_toFinset.mpr hs,eq⟩
    have low := Finset.card_le_card sub
    rw [Finset.card_image_of_injective _ inj] at low
    have high := Finset.card_image_le (s := (tr 0).toFinset) (f := fun s => location (M.addr s))
    have len := List.toFinset_card_le (tr 0)
    have budget := budgets 0
    simp only [Finset.card_univ,Fintype.card_fin] at low
    omega
  have surj : Function.Surjective (fun s : Q => (location (M.addr s)).getD 0) := by
    intro j
    by_cases zero : j = 0
    · obtain ⟨s,hs⟩ := partner
      exact ⟨s,by simp [hs,zero]⟩
    · let i : Fin 4 := ⟨j.val - 1, by omega⟩
      obtain ⟨s,hs⟩ := rights i
      refine ⟨s,?_⟩
      change (location (M.addr s)).getD 0 = j
      rw [hs]
      change rightLocation i = j
      apply Fin.ext
      simp only [rightLocation,i]
      have jpos : 0 < j.val := by by_contra hn; exact zero (Fin.ext (by omega))
      omega
  have running : 5 ≤ Fintype.card Q := by
    simpa using Fintype.card_le_of_surjective _ surj
  let select : Fin 5 → Fin 6 := ![0,2,3,4,5]
  have labels : ∀ j : Fin 5, label (select j) = j := by decide +kernel
  have haltInj : Function.Injective (fun j : Fin 5 => h (select j)) := by
    intro i j eq
    have targetEq := (outputs (select i)).symm.trans
      ((congrArg M.out eq).trans (outputs (select j)))
    simpa only [labels] using six_source_realization.2 targetEq
  have halting : 5 ≤ Fintype.card H := by
    simpa using Fintype.card_le_of_injective _ haltInj
  exact ⟨running,halting,by simpa only [Fintype.card_sum] using Nat.add_le_add running halting⟩

#print axioms three_call_state_obstruction
end D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore
