/- GID: D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction
   generality: I
   mirror-B: D5/B/S1/Recurrence/FibonacciPowerSumMod16Obstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Periodic Fibonacci residues modulo sixteen obstruct even perfect-power sums. -/

import Mathlib

namespace D5.S1.Recurrence.FibonacciPowerSumMod16Obstruction

/-- The complete set of square residues modulo sixteen. -/
def squareResidues16 : Finset ℕ := {0, 1, 4, 9}

private theorem fib_mod_sixteen_period_step :
    ∀ n : ℕ, Nat.fib (n + 24) % 16 = Nat.fib n % 16 := by
  intro n
  change Nat.fib (n + 24) ≡ Nat.fib n [MOD 16]
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n hn hn1 =>
      rw [show n + 2 + 24 = (n + 24) + 2 by omega,
        Nat.fib_add_two (n := n + 24), Nat.fib_add_two (n := n)]
      have hn1' : Nat.fib (n + 24 + 1) ≡ Nat.fib (n + 1) [MOD 16] := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn1
      exact hn.add hn1'

private theorem fib_mod_sixteen_reduction (n : ℕ) :
    Nat.fib n % 16 = Nat.fib (n % 24) % 16 := by
  have hsplit : n % 24 + 24 * (n / 24) = n := Nat.mod_add_div n 24
  have hmul : ∀ k : ℕ,
      Nat.fib (n % 24 + 24 * k) % 16 = Nat.fib (n % 24) % 16 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hp := fib_mod_sixteen_period_step (n % 24 + 24 * k)
        have hp' : Nat.fib (n % 24 + 24 * (k + 1)) % 16 =
            Nat.fib (n % 24 + 24 * k) % 16 := by
          simpa only [Nat.mul_succ, Nat.add_assoc] using hp
        exact hp'.trans ih
  exact (congrArg (fun t => Nat.fib t % 16) hsplit.symm).trans (hmul (n / 24))

/-- Fibonacci residues modulo sixteen have period twenty-four, and every index reduces to its
residue modulo twenty-four. -/
theorem fib_mod_sixteen_period :
    (∀ n : ℕ, Nat.fib (n + 24) % 16 = Nat.fib n % 16) ∧
      (∀ n : ℕ, Nat.fib n % 16 = Nat.fib (n % 24) % 16) := by
  exact ⟨fib_mod_sixteen_period_step, fib_mod_sixteen_reduction⟩

/-- Every natural-number square reduces modulo sixteen to one of `0`, `1`, `4`, and `9`. -/
theorem square_mod_sixteen :
    ∀ y : ℕ, y ^ 2 % 16 ∈ squareResidues16 := by
  intro y
  rw [Nat.pow_mod]
  have hy : y % 16 < 16 := Nat.mod_lt _ (by decide)
  interval_cases h : y % 16 <;> decide

/-- Ordered residue pairs whose Fibonacci sum is not a square residue modulo sixteen. -/
def E16 : Finset (Fin 24 × Fin 24) :=
  Finset.univ.filter fun (r, s) =>
    (Nat.fib r + Nat.fib s) % 16 ∉ squareResidues16

/-- Exactly 440 of the 576 ordered residue pairs give the modular obstruction. -/
theorem E16_card : E16.card = 440 := by
  set_option maxRecDepth 100000 in
  decide

private theorem even_power_sum_obstruction_main :
    ∀ n m : ℕ,
      (⟨n % 24, Nat.mod_lt _ (by decide)⟩,
        ⟨m % 24, Nat.mod_lt _ (by decide)⟩) ∈ E16 →
      ∀ y a : ℕ, Even a → 2 ≤ a → y ^ a ≠ Nat.fib n + Nat.fib m := by
  intro n m hbad y a ha htwo hpower
  rcases ha with ⟨k, rfl⟩
  cases k with
  | zero => omega
  | succ k =>
      have hsquare : (y ^ (k + 1)) ^ 2 % 16 ∈ squareResidues16 :=
        square_mod_sixteen (y ^ (k + 1))
      have hsum : (Nat.fib n + Nat.fib m) % 16 ∈ squareResidues16 := by
        rw [← hpower]
        simpa only [Nat.succ_eq_add_one, pow_add, pow_two] using hsquare
      have hresidue :
          (Nat.fib (n % 24) + Nat.fib (m % 24)) % 16 ∈ squareResidues16 := by
        rw [Nat.add_mod] at hsum ⊢
        rw [fib_mod_sixteen_period.2 n, fib_mod_sixteen_period.2 m] at hsum
        exact hsum
      exact (Finset.mem_filter.mp hbad).2 hresidue

/-- A residue pair in `E16` cannot support an even perfect-power Fibonacci sum; the companion
identity checks the largest numerical solution singled out in the source conjecture. -/
theorem even_power_sum_obstruction :
    (∀ n m : ℕ,
      (⟨n % 24, Nat.mod_lt _ (by decide)⟩,
        ⟨m % 24, Nat.mod_lt _ (by decide)⟩) ∈ E16 →
      ∀ y a : ℕ, Even a → 2 ≤ a → y ^ a ≠ Nat.fib n + Nat.fib m) ∧
      Nat.fib 36 + Nat.fib 12 = 3864 ^ 2 := by
  constructor
  · exact even_power_sum_obstruction_main
  · decide

-- Fidelity witnesses: the quantified domains are inhabited and the obstruction hypotheses occur.
example : ℕ := 0

example :
    (⟨3 % 24, Nat.mod_lt _ (by decide)⟩,
      ⟨0 % 24, Nat.mod_lt _ (by decide)⟩) ∈ E16 ∧ Even 2 ∧ 2 ≤ 2 := by
  decide

#print axioms fib_mod_sixteen_period
#print axioms square_mod_sixteen
#print axioms E16_card
#print axioms even_power_sum_obstruction

end D5.S1.Recurrence.FibonacciPowerSumMod16Obstruction
