/- GID: D5/S3/Factorization/Automata/GuardedPrimeProduct
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/GuardedPrimeProduct
   mirror-E: none(waiver:unbounded-arithmetic-state-minimality)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic]
   utility: none
   digest: Actual prime-product continuations distinguish every divisor state;
     the exact total guarded output automaton needs tau(N)+1 states. -/

import D5.S0.Automata.DFAOStateLowerBound
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.GuardedPrimeProduct

open D5.S0.Automata.DFAOStateLowerBound

/-- Inputs are actual prime divisors, not anonymous register labels. -/
abbrev Alphabet (N : Nat) := ↥N.primeFactors

/-- These are the live arithmetic states, before adding total rejection. -/
abbrev Live (N : Nat) := ↥N.divisors

/-- The integer represented by the entire prime-input word. -/
def value {N : Nat} (w : List (Alphabet N)) : Nat :=
  (w.map Subtype.val).prod

/-- The output asks whether every exponent still respects the capacity of N. -/
def target (N : Nat) (w : List (Alphabet N)) : Bool :=
  decide (value w ∣ N)

private theorem live_dvd {N : Nat} (d : Live N) : d.val ∣ N :=
  (Nat.mem_divisors.mp d.property).1

private theorem live_ne_zero {N : Nat} (hN : N ≠ 0) (d : Live N) : d.val ≠ 0 := by
  intro hz
  have h := live_dvd d
  rw [hz, Nat.zero_dvd_iff] at h
  exact hN h

private def oneState {N : Nat} (hN : N ≠ 0) : Live N :=
  ⟨1, Nat.mem_divisors.mpr ⟨one_dvd N, hN⟩⟩

private def fullState {N : Nat} (hN : N ≠ 0) : Live N :=
  ⟨N, Nat.mem_divisors.mpr ⟨dvd_refl N, hN⟩⟩

private def complement {N : Nat} (hN : N ≠ 0) (d : Live N) : Live N :=
  ⟨N / d.val, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (live_dvd d), hN⟩⟩

private def factorWord {N : Nat} (hN : N ≠ 0) (d : Live N) : List (Alphabet N) :=
  d.val.primeFactorsList.attach.map fun p =>
    ⟨p.val, Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactorsList p.property,
        (Nat.dvd_of_mem_primeFactorsList p.property).trans (live_dvd d), hN⟩⟩

private theorem factorWord_value {N : Nat} (hN : N ≠ 0) (d : Live N) :
    value (factorWord hN d) = d.val := by
  have hlist : (factorWord hN d).map Subtype.val = d.val.primeFactorsList := by
    simp [factorWord, List.map_map]
  rw [value, hlist]
  exact Nat.prod_primeFactorsList (live_ne_zero hN d)

private theorem value_append {N : Nat} (u v : List (Alphabet N)) :
    value (u ++ v) = value u * value v := by
  simp [value, List.map_append, List.prod_append]

private def step {N : Nat} (hN : N ≠ 0) :
    Option (Live N) → Alphabet N → Option (Live N)
  | none, _ => none
  | some d, p =>
      if h : d.val * p.val ∣ N then
        some ⟨d.val * p.val, Nat.mem_divisors.mpr ⟨h, hN⟩⟩
      else none

/-- Rejecting overflow is an actual absorbing state; legal states are not
silently saturated or wrapped. All live states output true. -/
def machine {N : Nat} (hN : N ≠ 0) :
    DFAO (Alphabet N) Bool (Option (Live N)) where
  start := some (oneState hN)
  step := step hN
  accept := ∅
  output := Option.isSome

private theorem eval_none {N : Nat} (hN : N ≠ 0) (w : List (Alphabet N)) :
    (machine hN).toDFA.evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      simpa [DFA.evalFrom_cons, machine, step] using ih

private theorem eval_live_output {N : Nat} (hN : N ≠ 0)
    (d : Live N) (w : List (Alphabet N)) :
    ((machine hN).toDFA.evalFrom (some d) w).isSome =
      decide (d.val * value w ∣ N) := by
  induction w generalizing d with
  | nil => simp [value, live_dvd]
  | cons p w ih =>
      rw [DFA.evalFrom_cons]
      change ((machine hN).toDFA.evalFrom (step hN (some d) p) w).isSome = _
      by_cases h : d.val * p.val ∣ N
      · rw [step, dif_pos h]
        rw [ih]
        simp [value, Nat.mul_assoc]
      · rw [step, dif_neg h, eval_none]
        have hn : ¬ d.val * value (p :: w) ∣ N := by
          intro hall
          apply h
          apply dvd_trans (show d.val * p.val ∣ d.val * value (p :: w) from ?_) hall
          exact ⟨value w, by simp [value, Nat.mul_assoc]⟩
        simp [hn]

private theorem correct {N : Nat} (hN : N ≠ 0) :
    ∀ w : List (Alphabet N), (machine hN).evalOutput w = target N w := by
  intro w
  simpa [DFAO.evalOutput, DFA.eval, machine, oneState, target] using
    eval_live_output hN (oneState hN) w

/-- The complement is not just a numerical witness: its actual prime
factorization is a common continuation separating incomparable divisor states. -/
private theorem complement_test {N : Nat} (hN : N ≠ 0) (d e : Live N) :
    e.val * (N / d.val) ∣ N ↔ e.val ∣ d.val := by
  have hc : N / d.val ≠ 0 := live_ne_zero hN (complement hN d)
  have heq : d.val * (N / d.val) = N := Nat.mul_div_cancel' (live_dvd d)
  have hcancel : e.val * (N / d.val) ∣ d.val * (N / d.val) ↔ e.val ∣ d.val :=
    mul_dvd_mul_iff_right hc
  simpa only [heq] using hcancel

private def overflowWord {N : Nat} (hN : N ≠ 0) (p : Alphabet N) :
    List (Alphabet N) := factorWord hN (fullState hN) ++ [p]

private theorem overflow_rejects {N : Nat} (hN : N ≠ 0) (p : Alphabet N) :
    target N (overflowWord hN p) = false := by
  have hp : p.val.Prime := (Nat.mem_primeFactors.mp p.property).1
  have hn : ¬ N * p.val ∣ N := by
    intro h
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
    have hlt : N < N * p.val := by
      simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.pos_of_ne_zero hN)
    omega
  simp [target, overflowWord, value_append, factorWord_value, fullState, value, hn]

private def prefix {N : Nat} (hN : N ≠ 0) (p : Alphabet N) :
    Option (Live N) → List (Alphabet N)
  | none => overflowWord hN p
  | some d => factorWord hN d

private def suffix {N : Nat} (hN : N ≠ 0) :
    Option (Live N) → Option (Live N) → List (Alphabet N)
  | some d, some e =>
      if e.val ∣ d.val then factorWord hN (complement hN e)
      else factorWord hN (complement hN d)
  | _, _ => []

private theorem separates {N : Nat} (hN : N ≠ 0) (p : Alphabet N)
    (s t : Option (Live N)) (hne : s ≠ t) :
    target N (prefix hN p s ++ suffix hN s t) ≠
      target N (prefix hN p t ++ suffix hN s t) := by
  cases s with
  | none =>
      cases t with
      | none => exact (hne rfl).elim
      | some e =>
          change target N (overflowWord hN p ++ []) ≠ target N (factorWord hN e ++ [])
          simp only [List.append_nil]
          rw [overflow_rejects]
          simp [target, factorWord_value, live_dvd]
  | some d =>
      cases t with
      | none =>
          change target N (factorWord hN d ++ []) ≠ target N (overflowWord hN p ++ [])
          simp only [List.append_nil]
          rw [overflow_rejects]
          simp [target, factorWord_value, live_dvd]
      | some e =>
          have hde : d.val ≠ e.val := by
            intro h
            apply hne
            exact congrArg some (Subtype.ext h)
          by_cases hed : e.val ∣ d.val
          · have hnd : ¬ d.val ∣ e.val := by
              intro hd
              exact hde (Nat.dvd_antisymm hd hed)
            have heq : e.val * (N / e.val) = N := Nat.mul_div_cancel' (live_dvd e)
            have hbad : ¬ d.val * (N / e.val) ∣ N :=
              fun h => hnd ((complement_test hN e d).mp h)
            simp [prefix, suffix, hed, target, value_append, factorWord_value,
              complement, heq, hbad]
          · have heq : d.val * (N / d.val) = N := Nat.mul_div_cancel' (live_dvd d)
            have hbad : ¬ e.val * (N / d.val) ∣ N :=
              fun h => hed ((complement_test hN d e).mp h)
            simp [prefix, suffix, hed, target, value_append, factorWord_value,
              complement, heq, hbad]

/-- Exact minimality for the actual prime alphabet and arithmetic target.
The supplied prime input excludes the exceptional empty alphabet N=1.
Correctness is on every word, including overflow; there is no assumed lower
bound or artificial full-state output in the hypotheses. -/
theorem arithmetic_dfao_minimality {N : Nat} (hN : N ≠ 0) (p : Alphabet N) :
    (∀ w, (machine hN).evalOutput w = target N w) ∧
    Fintype.card (Option (Live N)) = N.divisors.card + 1 ∧
    (∀ (S : Type) [Fintype S] (M : DFAO (Alphabet N) Bool S),
      (∀ w, M.evalOutput w = target N w) → N.divisors.card + 1 ≤ Fintype.card S) := by
  refine ⟨correct hN, by simp [Live], ?_⟩
  intro S _ M hM
  let cert : DistinguishingFamily Set.univ (target N) (Option (Live N)) :=
    { witnessPrefix := prefix hN p
      continuation := suffix hN
      left_mem := by intros; trivial
      right_mem := by intros; trivial
      target_ne := by intro s t hst; exact separates hN p s t hst }
  have hc := state_lower_bound_of_distinguishing_family M Set.univ (target N) cert
    (by intro w _; exact hM w)
  simpa [Live] using hc

#print axioms arithmetic_dfao_minimality

end D5.S3.Factorization.Automata.GuardedPrimeProduct
