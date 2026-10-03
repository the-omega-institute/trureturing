import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare

open _root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
open _root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun _ r x => (fibonacciRecurrencePolynomial (2 * r + 1)).eval x)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law a :=
    (∀ (r : ℕ), 119 ≤ r → ∀ (x : ℤ), 2 < x →
      128 * (6 : ℤ) ^ r < x ^ 2 - 4 →
      ¬ IsSquare (a.readout () r x)) ∧
    (∀ (r n : ℕ), 119 ≤ r → Odd n → 2 * r + 1 ≤ n →
      0 < Nat.fib ((2 * r + 1) * n) / Nat.fib n ∧
      ¬ IsSquare (Nat.fib ((2 * r + 1) * n) / Nat.fib n)) ∧
    (∀ (q k : ℕ), q.Prime → 239 ≤ q → 1 ≤ k →
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x0 : ℤ := 128 * 6 ^ 119 + 5
  have hpow : 0 ≤ (6 : ℤ) ^ 119 := pow_nonneg (by norm_num) _
  have hx : 2 < x0 := by
    dsimp [x0]
    nlinarith
  have hsize : 128 * (6 : ℤ) ^ 119 < x0 ^ 2 - 4 := by
    dsimp [x0]
    nlinarith [sq_nonneg ((6 : ℤ) ^ 119)]
  have hbad := h.1 119 (by decide) x0 hx hsize
  change ¬ IsSquare (0 : ℤ) at hbad
  exact hbad ⟨0, by norm_num⟩

noncomputable def registration : Registration arena
    ((∀ (r : ℕ), 119 ≤ r → ∀ (x : ℤ), 2 < x →
      128 * (6 : ℤ) ^ r < x ^ 2 - 4 →
      ¬ IsSquare ((fibonacciRecurrencePolynomial (2 * r + 1)).eval x)) ∧
    (∀ (r n : ℕ), 119 ≤ r → Odd n → 2 * r + 1 ≤ n →
      0 < Nat.fib ((2 * r + 1) * n) / Nat.fib n ∧
      ¬ IsSquare (Nat.fib ((2 * r + 1) * n) / Nat.fib n)) ∧
    (∀ (q k : ℕ), q.Prime → 239 ≤ q → 1 ≤ k →
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_recurrence_polynomial_nonsquare, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, (0 : ℤ), (1 : ℤ), ?_⟩
    change (fibonacciRecurrencePolynomial (2 * 1 + 1)).eval (0 : ℤ) ≠
      (fibonacciRecurrencePolynomial (2 * 1 + 1)).eval (1 : ℤ)
    norm_num [fibonacciRecurrencePolynomial]

register_information_theorem
  fibonacci_recurrence_polynomial_nonsquare
  in arena
  readout via (realize signature
    (fun _ r x => (fibonacciRecurrencePolynomial (2 * r + 1)).eval x)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body",
        "arg", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
