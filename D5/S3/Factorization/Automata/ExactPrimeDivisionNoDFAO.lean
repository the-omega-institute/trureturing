/- GID: D5/S3/Factorization/Automata/ExactPrimeDivisionNoDFAO
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/ExactPrimeDivisionNoDFAO
   mirror-E: none(waiver:unbounded-prime-continuation-obstruction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic]
   utility: none
   digest: Nontrivial prime-power divisibility on multiply-divide runs defeats finite automata. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.ExactPrimeDivisionNoDFAO

open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.TypedPartialDFAOOverBase

/-- A register holds a positive integer, starts at one, and reads a word over two
letters: `true` multiplies by the prime `p`, and `false` divides by `p` and is
undefined unless `p` divides the current value. A word is legal when every step is
defined. No automaton with finitely many states answers correctly, on every legal
word, whether `p ^ a` divides the integer reached, once `a` is positive. The
positional numeral model is a different question and is not addressed here. -/
theorem no_finite_dfao_for_exact_prime_division
    {p a : Nat} (hp : p.Prime) (ha : 0 < a)
    (register : PartialDFA Bool Nat) (hstart : register.start = 1)
    (hstep : ∀ n up, register.step n up =
      if up then some (n * p) else if p ∣ n then some (n / p) else none)
    (S : Type) [Finite S] (M : DFAO Bool Bool S) :
    ¬ M.CorrectOn {w | (register.eval w).isSome = true}
        (fun w => match register.eval w with
          | none => false
          | some n => decide (p ^ a ∣ n)) := by
  let _ : Fintype S := Fintype.ofFinite S
  let exponentStep : Nat → Bool → Option Nat := fun e up =>
    if up then some (e + 1) else
      match e with
      | 0 => none
      | k + 1 => some k
  let exponentBase : PartialDFA Bool Nat := { start := 0, step := exponentStep }
  have step_image (e : Nat) (up : Bool) :
      register.step (p ^ e) up = (exponentStep e up).map (fun k => p ^ k) := by
    rw [hstep]
    cases up with
    | true => simp [exponentStep, pow_succ]
    | false =>
        cases e with
        | zero => simp [exponentStep, hp.ne_one]
        | succ e =>
            have hd : p ∣ p ^ (e + 1) := ⟨p ^ e, by simp [pow_succ, Nat.mul_comm]⟩
            simp [exponentStep, pow_succ, hp.ne_zero]
  have run_image (e : Nat) (w : List Bool) :
      register.evalFrom (p ^ e) w =
        (exponentBase.evalFrom e w).map (fun k => p ^ k) := by
    induction w generalizing e with
    | nil => rfl
    | cons up w ih =>
        change runTransition register.step (p ^ e) (up :: w) =
          (runTransition exponentStep e (up :: w)).map (fun k => p ^ k)
        simp only [runTransition]
        rw [step_image]
        cases h : exponentStep e up with
        | none => simp
        | some k =>
            simpa [h, exponentBase, PartialDFA.evalFrom] using ih k
  have up_run (e n : Nat) :
      exponentBase.evalFrom e (List.replicate n true) = some (e + n) := by
    induction n generalizing e with
    | zero => simp [PartialDFA.evalFrom, runTransition]
    | succ n ih =>
        rw [List.replicate_succ]
        change exponentBase.evalFrom (e + 1) (List.replicate n true) = _
        rw [ih]
        congr 1
        omega
  have down_run (e n : Nat) (hn : n ≤ e) :
      exponentBase.evalFrom e (List.replicate n false) = some (e - n) := by
    induction n generalizing e with
    | zero => simp [PartialDFA.evalFrom, runTransition]
    | succ n ih =>
        cases e with
        | zero => omega
        | succ e =>
            rw [List.replicate_succ]
            change exponentBase.evalFrom e (List.replicate n false) = _
            rw [ih e (by omega)]
            simp
  have word_spec (e k : Nat) (hk : k ≤ e) :
      (register.eval (List.replicate e true ++ List.replicate k false)).isSome = true ∧
      (match register.eval (List.replicate e true ++ List.replicate k false) with
        | none => false
        | some n => decide (p ^ a ∣ n)) = decide (a ≤ e - k) := by
    have hc : exponentBase.eval
        (List.replicate e true ++ List.replicate k false) = some (e - k) := by
      rw [PartialDFA.eval, PartialDFA.evalFrom_append, up_run]
      simpa [exponentBase] using down_run e k hk
    have h0 := run_image 0 (List.replicate e true ++ List.replicate k false)
    rw [pow_zero] at h0
    have hr : register.eval (List.replicate e true ++ List.replicate k false) =
        some (p ^ (e - k)) := by
      rw [PartialDFA.eval, hstart, h0]
      simpa [PartialDFA.eval, exponentBase] using congrArg (Option.map (fun j => p ^ j)) hc
    rw [hr]
    refine ⟨rfl, ?_⟩
    simp [Nat.pow_dvd_pow_iff_le_right hp.one_lt]
  intro hc
  have certificate :
      DistinguishingFamily {w | (register.eval w).isSome = true}
        (fun w => match register.eval w with
          | none => false
          | some n => decide (p ^ a ∣ n))
        (Fin (Fintype.card S + 1)) := {
    witnessPrefix := fun i => List.replicate (a + i.val) true
    continuation := fun i j => List.replicate (min i.val j.val + 1) false
    left_mem := by
      intro i j _
      have hm := Nat.min_le_left i.val j.val
      exact (word_spec (a + i.val) (min i.val j.val + 1) (by omega)).1
    right_mem := by
      intro i j _
      have hm := Nat.min_le_right i.val j.val
      exact (word_spec (a + j.val) (min i.val j.val + 1) (by omega)).1
    target_ne := by
      intro i j hij
      have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hmi := Nat.min_le_left i.val j.val
      have hmj := Nat.min_le_right i.val j.val
      rw [(word_spec (a + i.val) (min i.val j.val + 1) (by omega)).2,
        (word_spec (a + j.val) (min i.val j.val + 1) (by omega)).2]
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · rw [min_eq_left hlt.le]
        have hi : ¬ a ≤ a + i.val - (i.val + 1) := by omega
        have hj : a ≤ a + j.val - (i.val + 1) := by omega
        simp [hi, hj]
      · rw [min_eq_right hgt.le]
        have hi : a ≤ a + i.val - (j.val + 1) := by omega
        have hj : ¬ a ≤ a + j.val - (j.val + 1) := by omega
        simp [hi, hj]
  }
  have hbound := state_lower_bound_of_distinguishing_family
    M {w | (register.eval w).isSome = true}
    (fun w => match register.eval w with
      | none => false
      | some n => decide (p ^ a ∣ n)) certificate hc
  simp only [Fintype.card_fin] at hbound
  omega

end D5.S3.Factorization.Automata.ExactPrimeDivisionNoDFAO
