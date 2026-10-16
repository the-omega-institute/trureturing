/- GID: D5/S0/Computability/BinaryMachine/Clock
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/Clock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine Clock supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/Clock.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.Classes
import Lean.Elab.Tactic.Omega

/-!
Explicit polynomial clocks for verifier computations. These lemmas turn the
unbounded acceptance predicate into bounded acceptance using the same concrete
machine and its proved all-input running-time bound.
-/

@[expose] public section

namespace Complexity

theorem powerBound_mono (c k : Nat) {n m : Nat} (h : n ≤ m) :
    powerBound c k n ≤ powerBound c k m := by
  exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) k)

@[simp] theorem pairWords_length (x y : Word) :
    (pairWords x y).length = 2 * x.length + 1 + y.length := by
  simp [pairWords, List.length_append, List.length_replicate]
  omega

/-- A concrete clock dominates a halting computation whenever one halting
observation within that clock is known. -/
theorem accepts_iff_at_clock (M : Machine) (input : Word) (clock : Nat)
    (hclock : ∃ time decision tape, time ≤ clock ∧
      runInput M time input = some (decision, tape)) :
    Accepts M input ↔ ∃ tape, runInput M clock input = some (true, tape) := by
  constructor
  · intro ⟨time, tape, hrun⟩
    obtain ⟨t, decision, finalTape, ht, hfinal⟩ := hclock
    have heq := run_deterministic M (initial M input) hrun hfinal
    have hb : decision = true := (congrArg Prod.fst heq).symm
    subst decision
    exact ⟨finalTape, run_mono M ht (initial M input) _ hfinal⟩
  · intro ⟨tape, hrun⟩
    exact ⟨clock, tape, hrun⟩

/-- The verifier horizon after substituting the polynomial certificate bound
into the length of the explicit pair encoding. -/
def verifierClock (timeCoefficient timeExponent witnessCoefficient witnessExponent n : Nat) : Nat :=
  powerBound timeCoefficient timeExponent
    (2 * n + 1 + powerBound witnessCoefficient witnessExponent n)

theorem paired_accepts_iff_at_clock (M : Machine) (tc tk wc wk : Nat)
    (hM : ∀ input : Word, ∃ time decision tape,
      time ≤ powerBound tc tk input.length ∧
      runInput M time input = some (decision, tape))
    (input witness : Word) (hw : witness.length ≤ powerBound wc wk input.length) :
    Accepts M (pairWords input witness) ↔
      ∃ tape, runInput M (verifierClock tc tk wc wk input.length)
        (pairWords input witness) = some (true, tape) := by
  apply accepts_iff_at_clock
  obtain ⟨time, decision, tape, ht, hr⟩ := hM (pairWords input witness)
  refine ⟨time, decision, tape, Nat.le_trans ht ?_, hr⟩
  apply powerBound_mono
  simp only [pairWords_length]
  omega

theorem pair_size_power_bound (wc wk n : Nat) :
    2 * n + 1 + powerBound wc wk n + 1 ≤ (wc + 4) * (n + 1) ^ (wk + 1) := by
  have hpow : (n + 1) ^ wk ≤ (n + 1) ^ (wk + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hn : n + 1 ≤ (n + 1) ^ (wk + 1) := Nat.le_pow (by omega)
  have hmul := Nat.mul_le_mul_left wc hpow
  rw [powerBound_eq, Nat.add_mul]
  omega

/-- An explicit monomial dominating the verifier horizon; no polynomial
algebra library or asymptotic notation is needed. -/
theorem verifierClock_le_powerBound (tc tk wc wk n : Nat) :
    verifierClock tc tk wc wk n ≤
      powerBound (tc * (wc + 4) ^ tk) ((wk + 1) * tk) n := by
  have hp := Nat.pow_le_pow_left (pair_size_power_bound wc wk n) tk
  have hm := Nat.mul_le_mul_left tc hp
  simpa [verifierClock, powerBound_eq, Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc] using hm

/-- Every NP language has a single explicit polynomial clock in the instance
length for all its bounded certificates. This is a preparation lemma for the
tableau; it is not a SAT reduction. -/
theorem inNP_clocked {L : Language} (hL : InNP L) :
    ∃ M : Machine, ∃ wc wk tc tk,
      ∀ input, L input ↔ ∃ witness : Word,
        witness.length ≤ powerBound wc wk input.length ∧
        ∃ tape, runInput M
          (powerBound (tc * (wc + 4) ^ tk) ((wk + 1) * tk) input.length)
          (pairWords input witness) = some (true, tape) := by
  obtain ⟨M, wc, wk, ⟨tc, tk, hM⟩, hL⟩ := hL
  refine ⟨M, wc, wk, tc, tk, ?_⟩
  intro input
  rw [hL]
  constructor
  · intro ⟨witness, hw, ha⟩
    have hsmall := (paired_accepts_iff_at_clock M tc tk wc wk hM input witness hw).mp ha
    obtain ⟨tape, ht⟩ := hsmall
    exact ⟨witness, hw, tape,
      run_mono M (verifierClock_le_powerBound tc tk wc wk input.length)
        (initial M (pairWords input witness)) _ ht⟩
  · intro ⟨witness, hw, tape, ht⟩
    exact ⟨witness, hw, _, tape, ht⟩

/-- A computed output cannot be longer than a polynomial: its bits have to
occur on the tape reached by the actual local computation. -/
theorem polyTime_output_length {f : Word → Word} (hf : PolyTime f) :
    ∃ c k, ∀ input : Word, (f input).length ≤ powerBound c k input.length := by
  obtain ⟨M, c, k, hM⟩ := hf
  refine ⟨1 + 2 * c, k + 1, ?_⟩
  intro input
  obtain ⟨time, tape, ht, hr, ho⟩ := hM input
  have hs := runInput_output_length_le M time input (true, tape) hr
  have hp : (input.length + 1) ^ k ≤ (input.length + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hn : input.length + 1 ≤ (input.length + 1) ^ (k + 1) := Nat.le_pow (by omega)
  have hc := Nat.mul_le_mul_left c hp
  rw [ho] at hs
  simp only [powerBound_eq] at ht ⊢
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  omega

end Complexity
