import D5.S3.Arith.Primes.FibonacciHalfBinomialFiniteSumValuation
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Arith.Primes.FibonacciHalfBinomialFiniteSumValuation

open _root_.D5.S3.Arith.Primes.FibonacciHalfBinomialFiniteSumValuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ n c =>
      ∑ m ∈ Finset.range (n + 1), Ring.choose (1 / 2 : ℚ) m * (c m : ℚ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 1 ≤ n) (c : ℕ → ℤ) (_hc : Odd (c n)),
    padicValRat 2 (r.readout () n c) =
      -((n : ℤ) + padicValNat 2 n.factorial)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by decide) (fun _ => 1) (by norm_num)
  change padicValRat 2 (0 : ℚ) =
    -((1 : ℤ) + padicValNat 2 (Nat.factorial 1)) at hbad
  rw [padicValRat.zero] at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ (n : ℕ) (_hn : 1 ≤ n) (c : ℕ → ℤ) (_hc : Odd (c n)),
      padicValRat 2
        (∑ m ∈ Finset.range (n + 1), Ring.choose (1 / 2 : ℚ) m * (c m : ℚ)) =
        -((n : ℤ) + padicValNat 2 n.factorial)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨half_binomial_finite_sum_valuation, rejected, rejected_law⟩
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
    let c0 : ℕ → ℤ := fun m => if m = 1 then 1 else 0
    let c1 : ℕ → ℤ := fun m => if m = 0 then 1 else if m = 1 then 1 else 0
    refine ⟨1, c0, c1, ?_⟩
    have hz : actual.readout () 1 c0 = 1 / 2 := by
      norm_num [actual, realize, c0, Finset.sum_range_succ]
    have ho : actual.readout () 1 c1 = 3 / 2 := by
      norm_num [actual, realize, c1, Finset.sum_range_succ]
    rw [hz, ho]
    norm_num

register_information_theorem half_binomial_finite_sum_valuation in arena
  readout via (realize signature
    (fun _ n c =>
      ∑ m ∈ Finset.range (n + 1), Ring.choose (1 / 2 : ℚ) m * (c m : ℚ))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciHalfBinomialFiniteSumValuation
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

open Lean in
run_meta do
  let env ← getEnv
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == ``half_binomial_finite_sum_valuation)
    | throwError "Finite half-binomial sum registration evidence is missing"
  match row.result with
  | .declaredValidated _ => pure ()
  | .declaredUnresolved diagnostic =>
      throwError "Finite half-binomial sum registration is unresolved: {diagnostic}"
  | .undeclared => throwError "Finite half-binomial sum registration is undeclared"

end Reg.D5.S3.Arith.Primes.FibonacciHalfBinomialFiniteSumValuation
