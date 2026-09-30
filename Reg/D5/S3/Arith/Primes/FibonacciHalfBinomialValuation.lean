import D5.S3.Arith.Primes.FibonacciHalfBinomialValuation
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Arith.Primes.FibonacciHalfBinomialValuation

open _root_.D5.S3.Arith.Primes.FibonacciHalfBinomialValuation
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
    (fun _ _ n => Ring.choose (1 / 2 : ℚ) n)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    padicValRat 2 (r.readout () () n) =
      -((n : ℤ) + padicValNat 2 n.factorial)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1
  change padicValRat 2 (0 : ℚ) =
    -((1 : ℤ) + padicValNat 2 (Nat.factorial 1)) at hbad
  rw [padicValRat.zero] at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ n : ℕ, padicValRat 2 (Ring.choose (1 / 2 : ℚ) n) =
      -((n : ℤ) + padicValNat 2 n.factorial)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨half_binomial_two_adic_valuation, rejected, rejected_law⟩
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
    change Ring.choose (1 / 2 : ℚ) 0 ≠ Ring.choose (1 / 2 : ℚ) 1
    norm_num

register_information_theorem half_binomial_two_adic_valuation in arena
  readout via (realize signature
    (fun _ _ n => Ring.choose (1 / 2 : ℚ) n)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciHalfBinomialValuation
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``half_binomial_two_adic_valuation)
    | throwError "Half-binomial valuation registration evidence is missing"
  match row.result with
  | .declaredValidated _ => pure ()
  | .declaredUnresolved diagnostic =>
      throwError "Half-binomial valuation registration is unresolved: {diagnostic}"
  | .undeclared => throwError "Half-binomial valuation registration is undeclared"

end Reg.D5.S3.Arith.Primes.FibonacciHalfBinomialValuation
