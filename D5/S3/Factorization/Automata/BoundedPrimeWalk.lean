/- GID: D5/S3/Factorization/Automata/BoundedPrimeWalk
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/BoundedPrimeWalk
   mirror-E: none(waiver:all-capacities-all-command-words)
   anchors: []
   utility: none
   digest: Bounded exponent walks are proved to be the actual guarded integer
     multiplication and exact division, with complete repeated-probe semantics. -/

import D5.S3.Factorization.Automata.ReversiblePrimeThreshold
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.BoundedPrimeWalk

open D5.S0.Automata.TypedPartialDFAOOverBase

/-- The existing unbounded arithmetic step, with the actual capacity p^a checked
at its output. False requests exact division, not rounded division. -/
def integerStep (p a n : Nat) (up : Bool) : Option Nat :=
  (ReversiblePrimeThreshold.numberStep p n up).bind fun next =>
    if next ∣ p ^ a then some next else none

/-- A live exponent is in the closed interval [0,a]. Undefined steps reject. -/
def step (a : Nat) (e : Fin (a + 1)) (up : Bool) : Option (Fin (a + 1)) :=
  if up then
    if h : e.val < a then some ⟨e.val + 1, by omega⟩ else none
  else
    if h : 0 < e.val then some ⟨e.val - 1, by have := e.isLt; omega⟩ else none

/-- Run the repository's partial-transition semantics on an actual command word. -/
def run (a : Nat) (e : Fin (a + 1)) (w : List Bool) : Option (Fin (a + 1)) :=
  runTransition (step a) e w

/-- The only output is whether the whole word executed without crossing a guard. -/
def accepts (a : Nat) (e : Fin (a + 1)) (w : List Bool) : Bool :=
  (run a e w).isSome

/-- Every integer intermediate and the exact failure outcome are preserved, for
all words. No final-displacement replacement discards intermediate guards. -/
theorem run_transport {p : Nat} (hp : p.Prime) (a : Nat)
    (e : Fin (a + 1)) (w : List Bool) :
    runTransition (integerStep p a) (p ^ e.val) w =
      (run a e w).map (fun f => p ^ f.val) := by
  have step_transport (e : Fin (a + 1)) (b : Bool) :
      integerStep p a (p ^ e.val) b = (step a e b).map (fun f => p ^ f.val) := by
    cases b with
    | true =>
        have hdiv : (p ^ e.val * p ∣ p ^ a) ↔ e.val < a := by
          rw [← pow_succ, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
          omega
        by_cases h : e.val < a <;>
          simp [integerStep, ReversiblePrimeThreshold.numberStep, step, hdiv, h, pow_succ]
    | false =>
        cases he : e.val with
        | zero =>
            simp [integerStep, ReversiblePrimeThreshold.numberStep, step, he, hp.ne_one]
        | succ k =>
            have hk : k ≤ a := by have := e.isLt; omega
            have hd : p ∣ p ^ (k + 1) := ⟨p ^ k, by simp [pow_succ, Nat.mul_comm]⟩
            have hka : p ^ k ∣ p ^ a :=
              (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr hk
            simp [integerStep, ReversiblePrimeThreshold.numberStep, step, he, hd,
              pow_succ, hp.ne_zero, hka]
  induction w generalizing e with
  | nil => rfl
  | cons b w ih =>
      change runTransition (integerStep p a) (p ^ e.val) (b :: w) =
        (runTransition (step a) e (b :: w)).map (fun f => p ^ f.val)
      simp only [runTransition]
      rw [step_transport]
      cases hs : step a e b with
      | none => simp [hs]
      | some f => simpa [hs, run] using ih f

/-- Repeated multiplication succeeds exactly up to the upper boundary. -/
theorem accepts_up (a : Nat) (e : Fin (a + 1)) (n : Nat) :
    accepts a e (List.replicate n true) = decide (e.val + n ≤ a) := by
  induction n generalizing e with
  | zero =>
      have he : e.val ≤ a := by have := e.isLt; omega
      simp [accepts, run, runTransition, he]
  | succ n ih =>
      unfold accepts at ih ⊢
      simp only [List.replicate_succ, run, runTransition]
      by_cases he : e.val < a
      · have hf : e.val + 1 < a + 1 := by omega
        simpa [run, step, he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (⟨e.val + 1, hf⟩ : Fin (a + 1))
      · have hn : ¬ e.val + (n + 1) ≤ a := by omega
        simp [step, he, hn]

/-- Repeated exact division succeeds exactly up to the lower boundary. -/
theorem accepts_down (a : Nat) (e : Fin (a + 1)) (n : Nat) :
    accepts a e (List.replicate n false) = decide (n ≤ e.val) := by
  induction n generalizing e with
  | zero => simp [accepts, run, runTransition]
  | succ n ih =>
      unfold accepts at ih ⊢
      simp only [List.replicate_succ, run, runTransition]
      by_cases he : 0 < e.val
      · have hf : e.val - 1 < a + 1 := by have := e.isLt; omega
        have hn : (n ≤ e.val - 1) ↔ n + 1 ≤ e.val := by omega
        simpa [run, step, he, hn]
          using ih (⟨e.val - 1, hf⟩ : Fin (a + 1))
      · have hn : ¬ n + 1 ≤ e.val := by omega
        simp [step, he, hn]

#print axioms run_transport
#print axioms accepts_up
#print axioms accepts_down

end D5.S3.Factorization.Automata.BoundedPrimeWalk
