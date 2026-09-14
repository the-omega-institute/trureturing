/- GID: D5/S3/Factorization/Automata/GuardedPrimeProduct
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/GuardedPrimeProduct
   mirror-E: none(waiver:unbounded-arithmetic-state-minimality)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Basic]
   utility: none
   digest: Prime-product continuations distinguish every divisor state and force exactly tau(N)+1 guarded states. -/

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

private def oneState {N : Nat} (hN : N ≠ 0) : Live N :=
  ⟨1, Nat.mem_divisors.mpr ⟨one_dvd N, hN⟩⟩

private def fullState {N : Nat} (hN : N ≠ 0) : Live N :=
  ⟨N, Nat.mem_divisors.mpr ⟨dvd_refl N, hN⟩⟩

private def complement {N : Nat} (hN : N ≠ 0) (d : Live N) : Live N :=
  ⟨N / d.val, Nat.mem_divisors.mpr
    ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp d.property).1, hN⟩⟩

private def factorWord {N : Nat} (hN : N ≠ 0) (d : Live N) : List (Alphabet N) :=
  d.val.primeFactorsList.attach.map fun p =>
    ⟨p.val, Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactorsList p.property,
        (Nat.dvd_of_mem_primeFactorsList p.property).trans
          (Nat.mem_divisors.mp d.property).1, hN⟩⟩

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

private def overflowWord {N : Nat} (hN : N ≠ 0) (p : Alphabet N) :
    List (Alphabet N) := factorWord hN (fullState hN) ++ [p]

private def prefixWord {N : Nat} (hN : N ≠ 0) (p : Alphabet N) :
    Option (Live N) → List (Alphabet N)
  | none => overflowWord hN p
  | some d => factorWord hN d

private def suffix {N : Nat} (hN : N ≠ 0) :
    Option (Live N) → Option (Live N) → List (Alphabet N)
  | some d, some e =>
      if e.val ∣ d.val then factorWord hN (complement hN e)
      else factorWord hN (complement hN d)
  | _, _ => []

/-- Exact minimality for the actual prime alphabet and arithmetic target.
The supplied prime input excludes the exceptional empty alphabet N=1.
Correctness is on every word, including overflow; there is no assumed lower
bound or artificial full-state output in the hypotheses. -/
theorem arithmetic_dfao_minimality {N : Nat} (hN : N ≠ 0) (p : Alphabet N) :
    (∀ w, (machine hN).evalOutput w = target N w) ∧
    Fintype.card (Option (Live N)) = N.divisors.card + 1 ∧
    (∀ (S : Type) [Fintype S] (M : DFAO (Alphabet N) Bool S),
      (∀ w, M.evalOutput w = target N w) → N.divisors.card + 1 ≤ Fintype.card S) := by
  have live_dvd (d : Live N) : d.val ∣ N :=
    (Nat.mem_divisors.mp d.property).1
  have live_ne_zero (d : Live N) : d.val ≠ 0 := by
    intro hz
    have h := live_dvd d
    rw [hz, Nat.zero_dvd] at h
    exact hN h
  have factorWord_value (d : Live N) : value (factorWord hN d) = d.val := by
    have hlist : (factorWord hN d).map Subtype.val = d.val.primeFactorsList := by
      simp [factorWord, List.map_map]
    rw [value, hlist]
    exact Nat.prod_primeFactorsList (live_ne_zero d)
  have value_append (u v : List (Alphabet N)) :
      value (u ++ v) = value u * value v := by
    simp [value, List.map_append, List.prod_append]
  have eval_none (w : List (Alphabet N)) :
      (machine hN).toDFA.evalFrom none w = none := by
    induction w with
    | nil => rfl
    | cons q w ih => simpa [DFA.evalFrom_cons, machine, step] using ih
  have eval_live_output (d : Live N) (w : List (Alphabet N)) :
      ((machine hN).toDFA.evalFrom (some d) w).isSome =
        decide (d.val * value w ∣ N) := by
    induction w generalizing d with
    | nil => simp [value, live_dvd]
    | cons q w ih =>
        rw [DFA.evalFrom_cons]
        change ((machine hN).toDFA.evalFrom (step hN (some d) q) w).isSome = _
        by_cases h : d.val * q.val ∣ N
        · rw [step, dif_pos h, ih]
          simp [value, Nat.mul_assoc]
        · rw [step, dif_neg h, eval_none]
          have hn : ¬ d.val * value (q :: w) ∣ N := by
            intro hall
            apply h
            apply dvd_trans (show d.val * q.val ∣ d.val * value (q :: w) from ?_) hall
            exact ⟨value w, by simp [value, Nat.mul_assoc]⟩
          simp [hn]
  have correct : ∀ w : List (Alphabet N), (machine hN).evalOutput w = target N w := by
    intro w
    simpa [DFAO.evalOutput, DFA.eval, machine, oneState, target] using
      eval_live_output (oneState hN) w
  have complement_test (d e : Live N) :
      e.val * (N / d.val) ∣ N ↔ e.val ∣ d.val := by
    have hc : N / d.val ≠ 0 := live_ne_zero (complement hN d)
    have heq : d.val * (N / d.val) = N := Nat.mul_div_cancel' (live_dvd d)
    have hcancel : e.val * (N / d.val) ∣ d.val * (N / d.val) ↔ e.val ∣ d.val :=
      mul_dvd_mul_iff_right hc
    simpa only [heq] using hcancel
  have overflow_rejects : target N (overflowWord hN p) = false := by
    have hp : p.val.Prime := (Nat.mem_primeFactors.mp p.property).1
    have hn : ¬ N * p.val ∣ N := by
      intro h
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
      have hlt : N < N * p.val := by
        simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.pos_of_ne_zero hN)
      omega
    have hv : value (overflowWord hN p) = N * p.val := by
      rw [overflowWord, value_append, factorWord_value]
      simp [fullState, value]
    unfold target
    rw [hv]
    simp [hn]
  have separates (s t : Option (Live N)) (hne : s ≠ t) :
      target N (prefixWord hN p s ++ suffix hN s t) ≠
        target N (prefixWord hN p t ++ suffix hN s t) := by
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
                fun h => hnd ((complement_test e d).mp h)
              simp [prefixWord, suffix, hed, target, value_append, factorWord_value,
                complement, heq, hbad]
            · have heq : d.val * (N / d.val) = N := Nat.mul_div_cancel' (live_dvd d)
              have hbad : ¬ e.val * (N / d.val) ∣ N :=
                fun h => hed ((complement_test d e).mp h)
              simp [prefixWord, suffix, hed, target, value_append, factorWord_value,
                complement, heq, hbad]
  refine ⟨correct, by simp [Live], ?_⟩
  intro S _ M hM
  let cert : DistinguishingFamily Set.univ (target N) (Option (Live N)) :=
    { witnessPrefix := prefixWord hN p
      continuation := suffix hN
      left_mem := by intros; trivial
      right_mem := by intros; trivial
      target_ne := by intro s t hst; exact separates s t hst }
  have hc := state_lower_bound_of_distinguishing_family M Set.univ (target N) cert
    (by intro w _; exact hM w)
  simpa [Live] using hc

#print axioms arithmetic_dfao_minimality

end D5.S3.Factorization.Automata.GuardedPrimeProduct
