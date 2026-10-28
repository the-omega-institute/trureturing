import D5.S1.Recurrence.GibonacciPowerGcdNormalization
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S1.Recurrence.GibonacciPowerGcdNormalization
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.GibonacciPowerGcdNormalization
noncomputable section

/-- The observed state is an arbitrary natural index of a signed seeded solution. -/
abbrev signature : Signature where
  Params := ℤ × ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p n => gibonacci p.1 p.2 n) (fun e => nomatch e)

abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Every clause of the original theorem is retained; one recurrence operand is observed. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a b : ℤ) (_hab : a ≠ 0 ∨ b ≠ 0)
    (k : ℕ) (_hk : 1 ≤ k) (e : ℕ) (_he : 3 ≤ e),
    let d : ℤ := Int.gcd a b
    0 < d ∧
    d * (a / d) = a ∧ d * (b / d) = b ∧
    Int.gcd (a / d) (b / d) = 1 ∧
    (gibonacci a b 0 = a ∧ gibonacci a b 1 = b ∧
      ∀ n, gibonacci a b (n + 2) = gibonacci a b (n + 1) + r.readout () (a, b) n) ∧
    (gibonacci (a / d) (b / d) 0 = a / d ∧
      gibonacci (a / d) (b / d) 1 = b / d ∧
      ∀ n, gibonacci (a / d) (b / d) (n + 2) =
        gibonacci (a / d) (b / d) (n + 1) + gibonacci (a / d) (b / d) n) ∧
    0 ≤ powerGcd a b k e ∧ 0 ≤ powerGcd (a / d) (b / d) k e ∧
    (∀ r : ℤ, r ∣ powerGcd a b k e ↔ ∀ t : ℕ, r ∣ windowSum a b k e t) ∧
    (∀ r : ℤ, r ∣ powerGcd (a / d) (b / d) k e ↔
      ∀ t : ℕ, r ∣ windowSum (a / d) (b / d) k e t) ∧
    powerGcd a b k e = d ^ e * powerGcd (a / d) (b / d) k e

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 0 1 (Or.inr one_ne_zero) 1 (by decide) 3 (by decide)
  have hc := hh.2.2.2.2.1.2.2 1
  norm_num [bad, realize, gibonacci, LinearRecurrence.mkSol, Real.fibRec] at hc

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 1), 0, 1, ?_⟩
  norm_num [actual, realize, gibonacci, LinearRecurrence.mkSol, Real.fibRec]

/-- Full-telescope equivalence, lawful actual family, intervention, sensitivity and dependence. -/
def evidence : Registration arena
    (∀ (a b : ℤ) (_hab : a ≠ 0 ∨ b ≠ 0)
    (k : ℕ) (_hk : 1 ≤ k) (e : ℕ) (_he : 3 ≤ e),
    let d : ℤ := Int.gcd a b
    0 < d ∧
    d * (a / d) = a ∧ d * (b / d) = b ∧
    Int.gcd (a / d) (b / d) = 1 ∧
    (gibonacci a b 0 = a ∧ gibonacci a b 1 = b ∧
      ∀ n, gibonacci a b (n + 2) = gibonacci a b (n + 1) + gibonacci a b n) ∧
    (gibonacci (a / d) (b / d) 0 = a / d ∧
      gibonacci (a / d) (b / d) 1 = b / d ∧
      ∀ n, gibonacci (a / d) (b / d) (n + 2) =
        gibonacci (a / d) (b / d) (n + 1) + gibonacci (a / d) (b / d) n) ∧
    0 ≤ powerGcd a b k e ∧ 0 ≤ powerGcd (a / d) (b / d) k e ∧
    (∀ r : ℤ, r ∣ powerGcd a b k e ↔ ∀ t : ℕ, r ∣ windowSum a b k e t) ∧
    (∀ r : ℤ, r ∣ powerGcd (a / d) (b / d) k e ↔
      ∀ t : ℕ, r ∣ windowSum (a / d) (b / d) k e t) ∧
    powerGcd a b k e = d ^ e * powerGcd (a / d) (b / d) k e) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def result_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S1.Recurrence.GibonacciPowerGcdNormalization.result)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S1.Recurrence.GibonacciPowerGcdNormalization.result_unit
  realizationName := `Reg.D5.S1.Recurrence.GibonacciPowerGcdNormalization.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => gibonacci p.1 p.2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Recurrence.GibonacciPowerGcdNormalization
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms result_registration

end
end Reg.D5.S1.Recurrence.GibonacciPowerGcdNormalization
