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

/-! Exact additive responses of the original binary scanner. -/

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
      ite_true, dite_eq_left hs, weight]
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
        simpa only [response_true, dite_eq_left hs, dite_eq_left ht] using
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
          · simp only [dite_eq_left hs, dite_eq_left ht] at ho
            simpa only [response_true, dite_eq_left hs, dite_eq_left ht] using ho w hl
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
    have hs := s.isLt
    have ht := t.isLt
    have hs' : min (k - s.val) 1 = 1 := by omega
    have ht' : min (k - t.val) 1 = 1 := by omega
    simp [SignatureEq, hs', ht']
  | succ h ih =>
    constructor
    · intro hf
      obtain ⟨huv, hz, ho⟩ := (future_succ c k hp h u n s v m t).mp hf
      obtain ⟨_, _, hz⟩ := (ih u (n + 1) ⟨0, hp⟩ v (m + 1) ⟨0, hp⟩).mp hz
      by_cases hs : s.val + 1 < k
      · by_cases ht : t.val + 1 < k
        · have ho' := (ih (u + c n) (n + 1) ⟨s.val + 1, hs⟩
            (v + c m) (m + 1) ⟨t.val + 1, ht⟩).mp (by simpa [hs, ht] using ho)
          obtain ⟨ho, hd, _⟩ := ho'
          have hc : c n = c m := by simpa [huv] using ho
          refine ⟨huv, ?_, ?_⟩
          · have hsk := s.isLt
            have htk := t.isLt
            dsimp only at hd
            omega
          · intro j hj _
            cases j with
            | zero => simpa using hc
            | succ j =>
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hz j (by omega) (Or.inl (by simp; omega))
        · simp [hs, ht] at ho
      · have ht : ¬t.val + 1 < k := by simpa [hs] using ho
        refine ⟨huv, ?_, ?_⟩
        · have hsk := s.isLt
          have htk := t.isLt
          omega
        · intro j hj hv
          have hj0 : 0 < j := by rcases hv with hv | hv <;> omega
          obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hz i (by omega) (Or.inl (by simp; omega))
    · rintro ⟨huv, hd, hc⟩
      apply (future_succ c k hp h u n s v m t).mpr
      have hz : ∀ j < h, c (n + 1 + j) = c (m + 1 + j) := by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc (j + 1) (by omega) (Or.inr (by omega))
      refine ⟨huv, ?_, ?_⟩
      · apply (ih u (n + 1) ⟨0, hp⟩ v (m + 1) ⟨0, hp⟩).mpr
        exact ⟨huv, rfl, fun j hj _ => hz j hj⟩
      · by_cases hs : s.val + 1 < k
        · by_cases ht : t.val + 1 < k
          · simp only [dite_eq_left hs, dite_eq_left ht]
            apply (ih (u + c n) (n + 1) ⟨s.val + 1, hs⟩
              (v + c m) (m + 1) ⟨t.val + 1, ht⟩).mpr
            have hfirst : c n = c m := by simpa using hc 0 (by omega) (Or.inl hs)
            refine ⟨by rw [huv, hfirst], ?_, fun j hj _ => hz j hj⟩
            have hsk := s.isLt
            have htk := t.isLt
            dsimp only
            omega
          · have hsk := s.isLt
            have htk := t.isLt
            omega
        · have hsk := s.isLt
          have htk := t.isLt
          have ht : ¬t.val + 1 < k := by omega
          simpa [hs] using ht

/-- The actual low-bit-first polynomial value in a commutative ring. -/
def polynomialValue {C : Type*} [CommRing C] (x : C) (w : List Bool) : C :=
  ∑ i : Fin w.length, if w.get i then x ^ i.val else 0

/-- The source output uses the original DBonacci scanner, with absorbing rejection. -/
def nativeReadout {C B : Type*} [CommRing C] [AddCommGroup B]
    (x : C) (lam : C →+ B) (k : ℕ) (w : List Bool) : Option B :=
  if DBonacciAdmissible k w.length w.get then some (lam (polynomialValue x w)) else none

/-- Equality of all actual binary-suffix responses within the given budget. -/
def NativeKernel {C B : Type*} [CommRing C] [AddCommGroup B]
    (x : C) (lam : C →+ B) (k h : ℕ) (w v : List Bool) : Prop :=
  ∀ a : List Bool, a.length ≤ h →
    nativeReadout x lam k (w ++ a) = nativeReadout x lam k (v ++ a)

private theorem weight_ofFn {B : Type*} [AddCommGroup B] (c : ℕ → B)
    (n l : ℕ) (w : Fin l → Bool) :
    weight c n (List.ofFn w) = ∑ i : Fin l, if w i then c (n + i.val) else 0 := by
  induction l generalizing n with
  | zero => simp [weight]
  | succ l ih =>
    rw [List.ofFn_succ, weight, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem weight_append {B : Type*} [AddCommGroup B] (c : ℕ → B)
    (n : ℕ) (w a : List Bool) :
    weight c n (w ++ a) = weight c n w + weight c (n + w.length) a := by
  induction w generalizing n with
  | nil => simp [weight]
  | cons b w ih =>
    simp only [List.cons_append, weight, List.length_cons, ih]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc]

private theorem native_weight {C B : Type*} [CommRing C] [AddCommGroup B]
    (x : C) (lam : C →+ B) (w : List Bool) :
    weight (fun n => lam (x ^ n)) 0 w = lam (polynomialValue x w) := by
  have he := weight_ofFn (fun n => lam (x ^ n)) 0 w.length w.get
  simp only [List.ofFn_get, Nat.zero_add] at he
  rw [he, polynomialValue, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

private theorem scanner_native (k : ℕ) (hk : 2 ≤ k) (w : List Bool) :
    DBonacciAdmissible k w.length w.get ↔
      (scanner k (by omega)).eval w ≠ none := by
  have he := D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators.actual_endpoint_operators
    (K := ℚ) k hk
  have hh := he.2.1 w.length w.get
  simpa only [List.ofFn_get, scanner, PartialDFA.eval] using hh

private theorem native_response {C B : Type*} [CommRing C] [AddCommGroup B]
    (x : C) (lam : C →+ B) (k : ℕ) (hk : 2 ≤ k) (w a : List Bool) :
    nativeReadout x lam k (w ++ a) =
      ((scanner k (by omega)).eval w).bind (fun s =>
        response (fun n => lam (x ^ n)) k (by omega)
          (lam (polynomialValue x w)) w.length s a) := by
  classical
  have hn (v : List Bool) : nativeReadout x lam k v =
      ((scanner k (by omega)).eval v).map
        (fun _ => weight (fun n => lam (x ^ n)) 0 v) := by
    simp only [nativeReadout, scanner_native k hk, ← native_weight]
    cases hh : (scanner k (by omega)).eval v <;> simp [hh]
  rw [hn]
  rw [PartialDFA.eval, PartialDFA.evalFrom_append]
  rw [weight_append, Nat.zero_add, native_weight]
  simp only [PartialDFA.eval]
  cases hh : (scanner k (by omega)).evalFrom (scanner k (by omega)).start w <;>
    simp only [hh, Option.bind_none, Option.map_none, Option.bind_none, Option.bind_some]
  rfl

/-- Every actual history has exactly the finite-future signature dictated by its
current additive value, original scanner tail and available coefficient window.
The two rejecting cases and the empty suffix are included. -/
theorem actual_history_kernel_signature {C B : Type*} [CommRing C] [AddCommGroup B]
    (x : C) (lam : C →+ B) (k : ℕ) (hk : 2 ≤ k) (h : ℕ) (w v : List Bool) :
    NativeKernel x lam k h w v ↔
      match (scanner k (by omega)).eval w, (scanner k (by omega)).eval v with
      | none, none => True
      | some s, some t =>
        SignatureEq (fun n => lam (x ^ n)) k h
          (lam (polynomialValue x w)) w.length s
          (lam (polynomialValue x v)) v.length t
      | _, _ => False := by
  cases hw : (scanner k (by omega)).eval w with
  | none =>
    cases hv : (scanner k (by omega)).eval v with
    | none =>
      simp only [hw, hv]
      constructor
      · intro _; trivial
      · intro _ a _
        simp only [native_response x lam k hk, hw, hv, Option.bind_none]
    | some t =>
      simp only [hw, hv]
      constructor
      · intro he
        have hh := he [] (by simp)
        simp only [native_response x lam k hk, hw, hv, Option.bind_none,
          Option.bind_some, response_nil] at hh
        contradiction
      · exact False.elim
  | some s =>
    cases hv : (scanner k (by omega)).eval v with
    | none =>
      simp only [hw, hv]
      constructor
      · intro he
        have hh := he [] (by simp)
        simp only [native_response x lam k hk, hw, hv, Option.bind_none,
          Option.bind_some, response_nil] at hh
        contradiction
      · exact False.elim
    | some t =>
      simp only [hw, hv]
      rw [← record_signature (fun n => lam (x ^ n)) k hk]
      constructor <;> intro he a ha <;>
        simpa only [native_response x lam k hk, hw, hv, Option.bind_some] using he a ha

#print axioms actual_history_kernel_signature

end D5.S1.Words.AdmissibleWords.KBonacciAdditiveFutureKernel
