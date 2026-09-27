/- GID: D5/S3/Observer/Budget/EqualityQueryScheduleNormalForm
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/EqualityQueryScheduleNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every identifying equality-query protocol on finite candidates admits a pointwise faster exhaustive schedule, with the final candidate identified by elimination. -/

import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Observer.Budget.EqualityQueryScheduleNormalForm

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

universe u

/-- A center query tests whether the target is that center. -/
def equalityReadout {α : Type u} [DecidableEq α] (center target : α) : Bool :=
  decide (target = center)

/-- Query the listed candidates in order, stopping on a hit and leaving the last
candidate unqueried because all earlier negative answers identify it. -/
def scan {α : Type u} : List α → PassiveProtocol α (fun _ => Bool)
  | [] => .stop
  | [_] => .stop
  | a :: b :: rest => .query a (fun hit => if hit then .stop else scan (b :: rest))

/-- A distinct candidate schedule identifies every listed target. Its query
count is the one-based position, capped at one less than the list length. -/
theorem scan_identifies_with_exact_depth {α : Type u} [DecidableEq α]
    (order : List α) (distinct : order.Nodup) :
    (∀ a ∈ order, ∀ b ∈ order,
      runPassiveProtocol equalityReadout (scan order) a =
        runPassiveProtocol equalityReadout (scan order) b → a = b) ∧
    (∀ a ∈ order,
      (runPassiveProtocol equalityReadout (scan order) a).length =
        min (order.idxOf a + 1) (order.length - 1)) := by
  induction order with
  | nil => simp
  | cons c rest ih =>
    cases rest with
    | nil => simp [scan, runPassiveProtocol]
    | cons d rest =>
      have hc := (List.nodup_cons.mp distinct).1
      obtain ⟨ident, depth⟩ := ih (List.nodup_cons.mp distinct).2
      constructor
      · intro a ha b hb same
        have heads := (List.cons.inj same).1
        have answers : equalityReadout c a = equalityReadout c b := by
          simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using heads
        by_cases hac : a = c
        · subst a
          exact (by simpa [equalityReadout] using answers.symm : b = c).symm
        · have hbc : b ≠ c := by
            intro hbc
            subst b
            simp [equalityReadout, hac] at answers
          have tails := (List.cons.inj same).2
          apply ident a (List.mem_cons.mp ha |>.resolve_left hac)
            b (List.mem_cons.mp hb |>.resolve_left hbc)
          simpa [scan, runPassiveProtocol, equalityReadout, hac, hbc] using tails
      · intro a ha
        by_cases hac : a = c
        · subst a
          simp [scan, runPassiveProtocol, equalityReadout]
        · have ham : a ∈ d :: rest := (List.mem_cons.mp ha).resolve_left hac
          have hdepth := depth a ham
          rw [List.idxOf_cons_ne _ (Ne.symm hac)]
          simp only [scan, runPassiveProtocol, equalityReadout, hac, decide_false,
            Bool.false_eq_true, ↓reduceIte, List.length_cons]
          change (runPassiveProtocol equalityReadout (scan (d :: rest)) a).length + 1 = _
          rw [hdepth]
          simp only [List.length_cons]
          omega

/-- Every zero-error equality-query tree has an exhaustive distinct schedule
that is no slower at any target. This includes trees with repeated centers,
queries outside the candidate set, and queries after identification. -/
theorem equality_protocol_schedule_normal_form {α : Type u} [DecidableEq α]
    (tree : PassiveProtocol α (fun _ => Bool)) (candidates : Finset α)
    (identifies : ∀ a ∈ candidates, ∀ b ∈ candidates,
      runPassiveProtocol equalityReadout tree a =
        runPassiveProtocol equalityReadout tree b → a = b) :
    ∃ order : List α, order.Nodup ∧ order.toFinset = candidates ∧
      (∀ a ∈ candidates, ∀ b ∈ candidates,
        runPassiveProtocol equalityReadout (scan order) a =
          runPassiveProtocol equalityReadout (scan order) b → a = b) ∧
      (∀ a ∈ candidates,
        (runPassiveProtocol equalityReadout (scan order) a).length =
          min (order.idxOf a + 1) (candidates.card - 1)) ∧
      (∀ a ∈ candidates,
        (runPassiveProtocol equalityReadout (scan order) a).length ≤
          (runPassiveProtocol equalityReadout tree a).length) := by
  have extract : ∀ (tree : PassiveProtocol α (fun _ => Bool)) (s : Finset α),
      (∀ a ∈ s, ∀ b ∈ s, runPassiveProtocol equalityReadout tree a =
        runPassiveProtocol equalityReadout tree b → a = b) →
      ∃ order : List α, order.Nodup ∧ order.toFinset = s ∧
        ∀ a ∈ s, min (order.idxOf a + 1) (s.card - 1) ≤
          (runPassiveProtocol equalityReadout tree a).length := by
    intro tree
    induction tree with
    | stop =>
      intro s hs
      have small : s.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => hs a ha b hb rfl)
      refine ⟨s.toList, Finset.nodup_toList _, Finset.toList_toFinset _, ?_⟩
      intro a ha
      simp [show s.card - 1 = 0 by omega, runPassiveProtocol]
    | query c next ih =>
      intro s hs
      by_cases small : s.card ≤ 1
      · refine ⟨s.toList, Finset.nodup_toList _, Finset.toList_toFinset _, ?_⟩
        intro a ha
        simp [show s.card - 1 = 0 by omega]
      · have hfalse : ∀ a ∈ s.erase c, ∀ b ∈ s.erase c,
            runPassiveProtocol equalityReadout (next false) a =
              runPassiveProtocol equalityReadout (next false) b → a = b := by
          intro a ha b hb same
          obtain ⟨hac, has⟩ := Finset.mem_erase.mp ha
          obtain ⟨hbc, hbs⟩ := Finset.mem_erase.mp hb
          apply hs a has b hbs
          simpa [runPassiveProtocol, equalityReadout, hac, hbc] using same
        obtain ⟨rest, hd, he, hb⟩ := ih false (s.erase c) hfalse
        by_cases hcs : c ∈ s
        · have cn : c ∉ rest := by
            intro h
            have : c ∈ s.erase c := he ▸ List.mem_toFinset.mpr h
            exact Finset.notMem_erase c s this
          refine ⟨c :: rest, List.nodup_cons.mpr ⟨cn, hd⟩, ?_, ?_⟩
          · simp [he, Finset.insert_erase hcs]
          · intro a ha
            by_cases hac : a = c
            · subst a
              simp only [List.idxOf_cons_self, zero_add, runPassiveProtocol,
                List.length_cons]
              omega
            · have hb' := hb a (Finset.mem_erase.mpr ⟨hac, ha⟩)
              have card := Finset.card_erase_of_mem hcs
              rw [List.idxOf_cons_ne _ (Ne.symm hac)]
              simp only [runPassiveProtocol, equalityReadout, hac, decide_false,
                List.length_cons]
              omega
        · have erase : s.erase c = s := Finset.erase_eq_of_notMem hcs
          refine ⟨rest, hd, he.trans erase, ?_⟩
          intro a ha
          have hac : a ≠ c := by rintro rfl; exact hcs ha
          have hb' := hb a (by rw [erase]; exact ha)
          rw [erase] at hb'
          simp only [runPassiveProtocol, equalityReadout, hac, decide_false,
            List.length_cons]
          omega
  obtain ⟨order, distinct, exhaustive, faster⟩ := extract tree candidates identifies
  obtain ⟨ident, depth⟩ := scan_identifies_with_exact_depth order distinct
  have length : order.length = candidates.card := by
    rw [← exhaustive, List.toFinset_card_of_nodup distinct]
  have mem (a : α) : a ∈ order ↔ a ∈ candidates := by
    rw [← exhaustive, List.mem_toFinset]
  refine ⟨order, distinct, exhaustive, ?_, ?_, ?_⟩
  · intro a ha b hb
    exact ident a ((mem a).mpr ha) b ((mem b).mpr hb)
  · intro a ha
    simpa only [length] using depth a ((mem a).mpr ha)
  · intro a ha
    rw [depth a ((mem a).mpr ha), length]
    exact faster a ha

#print axioms scan_identifies_with_exact_depth
#print axioms equality_protocol_schedule_normal_form

end D5.S3.Observer.Budget.EqualityQueryScheduleNormalForm
