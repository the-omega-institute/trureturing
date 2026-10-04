import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ n => (fibonacciRecurrencePolynomial (n + 3)).coeff.{0} n)
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciRecurrencePolynomialCoefficients") "fibonacci_recurrence_polynomial_coefficients") "Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients/Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ n => (fibonacciRecurrencePolynomial (n + 3)).coeff.{0} n)
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "fn", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
