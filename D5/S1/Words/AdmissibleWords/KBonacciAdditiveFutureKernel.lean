/- GID: D5/S1/Words/AdmissibleWords/KBonacciAdditiveFutureKernel
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciAdditiveFutureKernel
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Actual binary histories and their additive finite-future signatures. -/

import D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators
import D5.S1.Words.AdmissibleWords.KBonacciActualCommonImagePlateau
import D5.S1.Words.AdmissibleWords.KBonacciDirectConcatenation
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.LinearRecurrence

set_option autoImplicit false
noncomputable section
namespace D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators

/-- The original scanner; the state is the current run of true bits. -/
def scanner (k : ℕ) (hk : 0 < k) : PartialDFA Bool (Fin k) where
  start := ⟨0, hk⟩
  step s b := if b then
    if h : s.val + 1 < k then some ⟨s.val + 1, h⟩ else none
    else some ⟨0, hk⟩

/-- Low-bit-first additive value, retaining every actual zero position. -/
def weight {B : Type*} [AddCommGroup B] (c : ℕ → B) :
    ℕ → List Bool → B
  | _, [] => 0
  | n, b :: w => (if b then c n else 0) + weight c (n + 1) w

/-- Rejection is the value none, distinct from every legal output. -/
def response {B : Type*} [AddCommGroup B] (c : ℕ → B)
    (k : ℕ) (hk : 0 < k) (u : B) (n : ℕ) (s : Fin k) (w : List Bool) : Option B :=
  ((scanner k hk).evalFrom s w).map (fun _ => u + weight c n w)

/-- Every suffix of length at most h is tested, including the empty suffix. -/
def FutureEq {B : Type*} [AddCommGroup B] (c : ℕ → B)
    (k : ℕ) (hk : 0 < k) (h : ℕ)
    (u : B) (n : ℕ) (s : Fin k) (v : B) (m : ℕ) (t : Fin k) : Prop :=
  ∀ w : List Bool, w.length ≤ h →
    response c k hk u n s w = response c k hk v m t w

/-- Equality of the current value, truncated rejection distance, and observable window. -/
def SignatureEq {B : Type*} [AddCommGroup B] (c : ℕ → B)
    (k h : ℕ) (u : B) (n : ℕ) (s : Fin k) (v : B) (m : ℕ) (t : Fin k) : Prop :=
  u = v ∧ min (k - s.val) (h + 1) = min (k - t.val) (h + 1) ∧
    ∀ j < h, (s.val + 1 < k ∨ 0 < j) → c (n + j) = c (m + j)

private theorem response_nil {B : Type*} [AddCommGroup B]
    (c : ℕ → B) (k : ℕ) (hk : 0 < k) (u : B) (n : ℕ) (s : Fin k) :
    response c k hk u n s [] = some u := by
  simp [response, PartialDFA.evalFrom, runTransition, weight]

private theorem response_false {B : Type*} [AddCommGroup B]
    (c : ℕ → B) (k : ℕ) (hk : 0 < k) (u : B) (n : ℕ) (s : Fin k) (w : List Bool) :
    response c k hk u n s (false :: w) =
      response c k hk u (n + 1) ⟨0, hk⟩ w := by
  simp [response, PartialDFA.evalFrom, runTransition, scanner, weight]

private theorem response_true {B : Type*} [AddCommGroup B]
    (c : ℕ → B) (k : ℕ) (hk : 0 < k) (u : B) (n : ℕ) (s : Fin k) (w : List Bool) :
    response c k hk u n s (true :: w) =
      if hs : s.val + 1 < k then
        response c k hk (u + c n) (n + 1) ⟨s.val + 1, hs⟩ w
      else none := by
  by_cases hs : s.val + 1 < k
  · simp only [response, PartialDFA.evalFrom, runTransition, scanner,
      Bool.true_eq, if_true, dif_pos hs, weight]
    cases (runTransition (scanner k hk).step ⟨s.val + 1, hs⟩ w) <;>
      simp [add_assoc]
  · simp [response, PartialDFA.evalFrom, runTransition, scanner, hs]

private theorem future_zero {B : Type*} [AddCommGroup B]
    (c : ℕ → B) (k : ℕ) (hk : 0 < k)
    (u : B) (n : ℕ) (s : Fin k) (v : B) (m : ℕ) (t : Fin k) :
    FutureEq c k hk 0 u n s v m t ↔ u = v := by
  constructor
  · intro he
    simpa only [response_nil, Option.some.injEq] using he [] (by simp)
  · intro he w hw
    have hw' : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    simp [response_nil, he]

private theorem future_succ {B : Type*} [AddCommGroup B]
    (c : ℕ → B) (k : ℕ) (hk : 0 < k) (h : ℕ)
    (u : B) (n : ℕ) (s : Fin k) (v : B) (m : ℕ) (t : Fin k) :
    FutureEq c k hk (h + 1) u n s v m t ↔
      u = v ∧
      FutureEq c k hk h u (n + 1) ⟨0, hk⟩ v (m + 1) ⟨0, hk⟩ ∧
      (if hs : s.val + 1 < k then
        if ht : t.val + 1 < k then
          FutureEq c k hk h (u + c n) (n + 1) ⟨s.val + 1, hs⟩
            (v + c m) (m + 1) ⟨t.val + 1, ht⟩
        else False
      else ¬ t.val + 1 < k) := by
  constructor
  · intro he
    have huv : u = v := by
      simpa only [response_nil, Option.some.injEq] using he [] (by simp)
    refine ⟨huv, ?_, ?_⟩
    · intro w hw
      simpa only [response_false] using he (false :: w) (by simp; omega)
    · split_ifs with hs ht
      · intro w hw
        simpa only [response_true, dif_pos hs, dif_pos ht] using
          he (true :: w) (by simp; omega)
      · have hh := he [true] (by simp)
        simp [response_true, hs, ht, response_nil] at hh
      · intro ht
        have hh := he [true] (by simp)
        simp [response_true, hs, ht, response_nil] at hh
  · rintro ⟨huv, hz, ho⟩ w hw
    cases w with
    | nil => simp [response_nil, huv]
    | cons b w =>
      have hl : w.length ≤ h := by simp only [List.length_cons] at hw; omega
      cases b with
      | false => simpa only [response_false] using hz w hl
      | true =>
        by_cases hs : s.val + 1 < k
        · by_cases ht : t.val + 1 < k
          · simp only [dif_pos hs, dif_pos ht] at ho
            simpa only [response_true, dif_pos hs, dif_pos ht] using ho w hl
          · simp [hs, ht] at ho
        · have ht : ¬t.val + 1 < k := by simpa [hs] using ho
          simp [response_true, hs, ht]

private theorem record_signature {B : Type*} [AddCommGroup B]
    (c : ℕ → B) (k : ℕ) (hk : 2 ≤ k) (h : ℕ)
    (u : B) (n : ℕ) (s : Fin k) (v : B) (m : ℕ) (t : Fin k) :
    FutureEq c k (by omega) h u n s v m t ↔
      SignatureEq c k h u n s v m t := by
  have hp : 0 < k := by omega
  induction h generalizing u n s v m t with
  | zero =>
    rw [future_zero]
    simp only [SignatureEq, Nat.zero_add, not_lt_zero', false_implies, implies_true,
      and_true]
    have hs := s.isLt
    have ht := t.isLt
    have hs' : min (k - s.val) 1 = 1 := by omega
    have ht' : min (k - t.val) 1 = 1 := by omega
    simp [hs', ht']
  | succ h ih =>
    rw [future_succ, ih]
    by_cases hs : s.val + 1 < k
    · by_cases ht : t.val + 1 < k
      · rw [dif_pos hs, dif_pos ht, ih]
        constructor
        · rintro ⟨huv, hz, ho⟩
          rcases hz with ⟨_, _, hz⟩
          rcases ho with ⟨ho, hd, _⟩
          have hc : c n = c m := by simpa [huv] using ho
          refine ⟨huv, ?_, ?_⟩
          · dsimp only [SignatureEq] at hd ⊢
            have hsk := s.isLt
            have htk := t.isLt
            dsimp only at hd
            omega
          · intro j hj _
            cases j with
            | zero => simpa using hc
            | succ j =>
              have hj' : j < h := by omega
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hz j hj' (Or.inl (by simp; omega))
        · rintro ⟨huv, hd, hc⟩
          have hfirst : c n = c m := by simpa using hc 0 (by omega) (Or.inl hs)
          have hz : ∀ j < h, c (n + 1 + j) = c (m + 1 + j) := by
            intro j hj
            simpa only [Nat.add_assoc] using hc (j + 1) (by omega) (Or.inl hs)
          refine ⟨huv, ⟨huv, rfl, fun j hj _ => hz j hj⟩, ?_⟩
          refine ⟨by rw [huv, hfirst], ?_, fun j hj _ => hz j hj⟩
          have hsk := s.isLt
          have htk := t.isLt
          dsimp only
          omega
      · rw [dif_pos hs, dif_neg ht]
        constructor
        · rintro ⟨_, _, hf⟩; exact hf.elim
        · rintro ⟨_, hd, _⟩
          have hsk := s.isLt
          have htk := t.isLt
          omega
    · rw [dif_neg hs]
      by_cases ht : t.val + 1 < k
      · constructor
        · rintro ⟨_, _, hn⟩; exact (hn ht).elim
        · rintro ⟨_, hd, _⟩
          have hsk := s.isLt
          have htk := t.isLt
          omega
      · constructor
        · rintro ⟨huv, ⟨_, _, hz⟩, _⟩
          refine ⟨huv, ?_, ?_⟩
          · have hsk := s.isLt
            have htk := t.isLt
            omega
          · intro j hj hv
            have hj0 : 0 < j := by rcases hv with hv | hv <;> omega
            obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hz i (by omega) (Or.inl (by simp; omega))
        · rintro ⟨huv, _, hc⟩
          refine ⟨huv, ⟨huv, rfl, ?_⟩, ht⟩
          intro j hj _
          simpa only [Nat.add_assoc] using
            hc (j + 1) (by omega) (Or.inr (by omega))

end D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel
