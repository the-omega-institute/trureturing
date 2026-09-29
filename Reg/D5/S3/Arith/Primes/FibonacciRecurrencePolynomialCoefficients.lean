import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients

open _root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun _ _ n => (fibonacciRecurrencePolynomial (n + 3)).coeff n)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law x :=
    (∀ n : ℕ, (fibonacciRecurrencePolynomial (n + 1)).natDegree = n ∧
      (fibonacciRecurrencePolynomial (n + 1)).coeff n = 1) ∧
    (∀ n : ℕ, x.readout () () n = (n + 1 : ℤ)) ∧
    (∀ r : ℕ, 1 ≤ r →
      (fibonacciRecurrencePolynomial (2 * r + 1)).coeff (2 * r - 2) =
        (2 * r - 1 : ℤ) ∧ Odd (2 * r - 1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.2.1 0
  change (0 : ℤ) = 1 at hbad
  norm_num at hbad

noncomputable def registration : Registration arena
    ((∀ n : ℕ, (fibonacciRecurrencePolynomial (n + 1)).natDegree = n ∧
        (fibonacciRecurrencePolynomial (n + 1)).coeff n = 1) ∧
      (∀ n : ℕ, (fibonacciRecurrencePolynomial (n + 3)).coeff n = (n + 1 : ℤ)) ∧
      (∀ r : ℕ, 1 ≤ r →
        (fibonacciRecurrencePolynomial (2 * r + 1)).coeff (2 * r - 2) =
          (2 * r - 1 : ℤ) ∧ Odd (2 * r - 1))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_recurrence_polynomial_coefficients, rejected, rejected_law⟩
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
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (fibonacciRecurrencePolynomial 3).coeff 0 ≠
      (fibonacciRecurrencePolynomial 4).coeff 1
    norm_num [fibonacciRecurrencePolynomial]

register_information_theorem
  fibonacci_recurrence_polynomial_coefficients
  in arena
  readout via (realize signature
    (fun _ _ n => (fibonacciRecurrencePolynomial (n + 3)).coeff n)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
