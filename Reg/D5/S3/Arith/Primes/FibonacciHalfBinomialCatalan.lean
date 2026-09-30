import D5.S3.Arith.Primes.FibonacciHalfBinomialCatalan
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Arith.Primes.FibonacciHalfBinomialCatalan

open _root_.D5.S3.Arith.Primes.FibonacciHalfBinomialCatalan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ n => Ring.choose (1 / 2 : ℚ) (n + 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    r.readout () () n =
        (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) ∧
      ∃ z : ℤ, (2 : ℚ)^(2*n + 1) * r.readout () () n = (z : ℚ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 0).1
  change (0 : ℚ) =
    (-1 : ℚ)^0 * (catalan 0 : ℚ) / (2 : ℚ)^(2*0 + 1) at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ n : ℕ,
      Ring.choose (1 / 2 : ℚ) (n + 1) =
          (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) ∧
        ∃ z : ℤ, (2 : ℚ)^(2*n + 1) *
          Ring.choose (1 / 2 : ℚ) (n + 1) = (z : ℚ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨half_binomial_catalan, rejected, rejected_law⟩
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
    change Ring.choose (1 / 2 : ℚ) 1 ≠ Ring.choose (1 / 2 : ℚ) 2
    have htwo := (half_binomial_catalan 1).1
    norm_num at htwo
    rw [htwo]
    norm_num

register_information_theorem half_binomial_catalan in arena
  readout via (realize signature
    (fun _ _ n => Ring.choose (1 / 2 : ℚ) (n + 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciHalfBinomialCatalan
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``half_binomial_catalan)
    | throwError "Half-binomial Catalan registration evidence is missing"
  match row.result with
  | .declaredValidated _ => pure ()
  | .declaredUnresolved diagnostic =>
      throwError "Half-binomial Catalan registration is unresolved: {diagnostic}"
  | .undeclared => throwError "Half-binomial Catalan registration is undeclared"

end Reg.D5.S3.Arith.Primes.FibonacciHalfBinomialCatalan
