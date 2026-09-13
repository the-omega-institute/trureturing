/- GID: D5/S3/Factorization/Automata/ReversiblePrimeThreshold
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/ReversiblePrimeThreshold
   mirror-E: none(waiver:unbounded-prime-continuation-obstruction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic]
   utility: none
   digest: Exact multiplication and division by one prime force unbounded
     predictive state even for a fixed divisibility threshold and legal inputs. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.ReversiblePrimeThreshold

open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.TypedPartialDFAOOverBase

/-- True means actual integer multiplication; false means exact division.
Division is undefined unless its arithmetic divisibility guard holds. -/
def numberStep (p n : Nat) (up : Bool) : Option Nat :=
  if up then some (n * p) else if p ∣ n then some (n / p) else none

/-- The actual unbounded prime-power register starts at the integer one. -/
def primeBase (p : Nat) : PartialDFA Bool Nat where
  start := 1
  step n up := numberStep p n up

/-- Correctness will only be requested on executable words. -/
def legal (p : Nat) : Set (List Bool) :=
  {w | ((primeBase p).eval w).isSome = true}

/-- This is an arithmetic property of the reached integer, not the full
exponent as an output. The default on illegal words is not used by the theorem. -/
def target (p a : Nat) (w : List Bool) : Bool :=
  match (primeBase p).eval w with
  | none => false
  | some n => decide (p ^ a ∣ n)

private def exponentStep (e : Nat) (up : Bool) : Option Nat :=
  if up then some (e + 1) else
    match e with
    | 0 => none
    | k + 1 => some k

private def exponentBase : PartialDFA Bool Nat where
  start := 0
  step := exponentStep

private theorem step_image {p : Nat} (hp : p.Prime) (e : Nat) (up : Bool) :
    numberStep p (p ^ e) up = (exponentStep e up).map (fun k => p ^ k) := by
  cases up with
  | true => simp [numberStep, exponentStep, pow_succ]
  | false =>
      cases e with
      | zero => simp [numberStep, exponentStep, hp.ne_one]
      | succ e =>
          have hd : p ∣ p ^ (e + 1) := ⟨p ^ e, by simp [pow_succ, Nat.mul_comm]⟩
          simp [numberStep, exponentStep, hd, pow_succ, hp.ne_zero]

/-- The exponent coordinates are proved to simulate the actual integer
operations; they are not silently substituted for another transition system. -/
private theorem run_image {p : Nat} (hp : p.Prime) (e : Nat) (w : List Bool) :
    (primeBase p).evalFrom (p ^ e) w =
      (exponentBase.evalFrom e w).map (fun k => p ^ k) := by
  induction w generalizing e with
  | nil => rfl
  | cons up w ih =>
      change runTransition (numberStep p) (p ^ e) (up :: w) =
        (runTransition exponentStep e (up :: w)).map (fun k => p ^ k)
      simp only [runTransition]
      rw [step_image hp]
      cases h : exponentStep e up with
      | none => simp [h]
      | some k =>
          simpa [h, primeBase, exponentBase, PartialDFA.evalFrom] using ih k

private theorem up_run (e n : Nat) :
    exponentBase.evalFrom e (List.replicate n true) = some (e + n) := by
  induction n generalizing e with
  | zero => simp [PartialDFA.evalFrom, runTransition]
  | succ n ih =>
      rw [List.replicate_succ]
      change exponentBase.evalFrom e (true :: List.replicate n true) = _
      change exponentBase.evalFrom (e + 1) (List.replicate n true) = _
      rw [ih]
      congr 1
      omega

private theorem down_run (e n : Nat) (hn : n ≤ e) :
    exponentBase.evalFrom e (List.replicate n false) = some (e - n) := by
  induction n generalizing e with
  | zero => simp [PartialDFA.evalFrom, runTransition]
  | succ n ih =>
      cases e with
      | zero => omega
      | succ e =>
          rw [List.replicate_succ]
          change exponentBase.evalFrom (e + 1) (false :: List.replicate n false) = _
          change exponentBase.evalFrom e (List.replicate n false) = _
          rw [ih e (by omega)]
          simp

private theorem word_spec {p : Nat} (hp : p.Prime) (a e k : Nat) (hk : k ≤ e) :
    (List.replicate e true ++ List.replicate k false) ∈ legal p ∧
    target p a (List.replicate e true ++ List.replicate k false) =
      decide (a ≤ e - k) := by
  have hc : exponentBase.eval
      (List.replicate e true ++ List.replicate k false) = some (e - k) := by
    rw [PartialDFA.eval, PartialDFA.evalFrom_append, up_run]
    simpa [exponentBase] using down_run e k hk
  have hr := run_image hp 0 (List.replicate e true ++ List.replicate k false)
  change (primeBase p).eval
      (List.replicate e true ++ List.replicate k false) =
    (exponentBase.eval
      (List.replicate e true ++ List.replicate k false)).map (fun j => p ^ j) at hr
  rw [hc] at hr
  simp only [Option.map_some] at hr
  constructor
  · simp [legal, hr]
  · simp [target, hr, Nat.pow_dvd_pow_iff_le_right hp.one_lt]

/-- An arbitrary finite set of exponent states has explicit pairwise shared
legal suffixes. The observation is only the Boolean p^a divisibility test. -/
private def certificate {p a : Nat} (hp : p.Prime) (ha : 0 < a) (H : Nat) :
    DistinguishingFamily (legal p) (target p a) (Fin (H + 1)) where
  witnessPrefix i := List.replicate (a + i.val) true
  continuation i j := List.replicate (min i.val j.val + 1) false
  left_mem := by
    intro i j _
    have hm := Nat.min_le_left i.val j.val
    exact (word_spec hp a (a + i.val) (min i.val j.val + 1) (by omega)).1
  right_mem := by
    intro i j _
    have hm := Nat.min_le_right i.val j.val
    exact (word_spec hp a (a + j.val) (min i.val j.val + 1) (by omega)).1
  target_ne := by
    intro i j hij
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hmi := Nat.min_le_left i.val j.val
    have hmj := Nat.min_le_right i.val j.val
    rw [(word_spec hp a (a + i.val) (min i.val j.val + 1) (by omega)).2,
      (word_spec hp a (a + j.val) (min i.val j.val + 1) (by omega)).2]
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · rw [min_eq_left hlt.le]
      have hi : ¬ a ≤ a + i.val - (i.val + 1) := by omega
      have hj : a ≤ a + j.val - (i.val + 1) := by omega
      simp [hi, hj]
    · rw [min_eq_right hgt.le]
      have hi : a ≤ a + i.val - (j.val + 1) := by omega
      have hj : ¬ a ≤ a + j.val - (j.val + 1) := by omega
      simp [hi, hj]

/-- No finite-state output automaton computes the fixed prime divisibility
threshold for all legal multiply/divide histories. This excludes neither
bounded registers nor algorithms supplied with the integer's digits anew.
The lower bound is forced by actual positive-integer paths on p^e. -/
theorem no_finite_dfao_for_exact_prime_division
    {p a : Nat} (hp : p.Prime) (ha : 0 < a)
    (S : Type) [Fintype S] (M : DFAO Bool Bool S) :
    ¬ M.CorrectOn (legal p) (target p a) := by
  intro hc
  have hbound := state_lower_bound_of_distinguishing_family
    M (legal p) (target p a) (certificate hp ha (Fintype.card S)) hc
  simp only [Fintype.card_fin] at hbound
  omega

#print axioms no_finite_dfao_for_exact_prime_division

end D5.S3.Factorization.Automata.ReversiblePrimeThreshold
