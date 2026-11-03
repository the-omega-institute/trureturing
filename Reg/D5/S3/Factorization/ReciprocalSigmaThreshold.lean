import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Factorization.ReciprocalSigmaThreshold

/-! Source-bound audit of both all-positive-threshold leastness predicates. -/

namespace Reg.D5.S3.Factorization.ReciprocalSigmaThreshold
open _root_.D5.S3.Factorization.ReciprocalSigmaThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
noncomputable section

/-- Observe both predicates on the entire natural domain, with positivity retained in the law. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => g k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, 0 < r → ∃ m : ℕ,
    IsLeast {k : ℕ | 0 < k ∧ ⌊R.readout false () k⌋ = (r : ℤ)} m ∧
    IsLeast {k : ℕ | 0 < k ∧ (r : ℚ) ≤ R.readout true () k} m

/-- Vary one complete family while keeping the other readout fixed. -/
def rejected (i : Bool) : Realization signature :=
  realize signature (fun j _ k => if j = i then 0 else g k) (fun e => nomatch e)

private theorem rejected_fails (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  obtain ⟨m, hf, ht⟩ := h 1 (by decide)
  cases i
  · have bad := hf.1.2
    norm_num [rejected, realize] at bad
  · have bad := ht.1.2
    norm_num [rejected, realize] at bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize, g, ArithmeticFunction.sigma_one_apply, Nat.prime_two.divisors]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected false, rejected_fails false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_fails i⟩
      intro j hji
      funext p k
      simp [actual, rejected, realize, hji]
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Factorization.ReciprocalSigmaThreshold.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.ReciprocalSigmaThreshold.unit
  realizationName := `Reg.D5.S3.Factorization.ReciprocalSigmaThreshold.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => g k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.ReciprocalSigmaThreshold
    definition := some {
      owner := `D5.S3.Factorization.ReciprocalSigmaThreshold
      name := `D5.S3.Factorization.ReciprocalSigmaThreshold.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg", "fn", "arg",
        "body", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Factorization.ReciprocalSigmaThreshold
