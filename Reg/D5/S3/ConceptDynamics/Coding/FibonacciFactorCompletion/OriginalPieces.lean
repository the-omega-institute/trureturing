import Reg.Support.FibonacciOriginalSourceWitness.Source130
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces
noncomputable section

abbrev suffixSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : List Label, ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def suffixActual : Realization suffixSignature :=
  realize suffixSignature (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e)

def suffixRejected : Realization suffixSignature :=
  realize suffixSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev suffixArena : Arena.{0,0,0,0,0} where
  signature := suffixSignature
  Law r := ∀ (A : List Label) (pieces : ℕ → Set ℝ) (z : ℝ)
    (terminal : z ∈ pieces A.length)
    (edges : ∀ p (hp : p < A.length), ∀ y ∈ pieces (p+1), branch A[p] y ∈ pieces p),
    ∀ p, p ≤ A.length → r.readout () ⟨A, z⟩ p ∈ pieces p

/-- A one-edge path has an inhabited terminal piece and an unrestricted initial piece. -/
theorem suffix_rejected_law : ¬ suffixArena.Law suffixRejected := by
  intro h
  have hh := h [Label.L2] (fun p => if p = 0 then Set.univ else {0}) 0
    (by simp)
    (by
      intro p hp y hy
      have hp0 : p = 0 := by simpa using hp
      subst p
      simp)
    1 (by simp)
  norm_num [suffixRejected, realize] at hh

def suffixRegistration : Registration suffixArena (type_of% @original_piece_suffix_membership) where
  actual := suffixActual
  bridge := Iff.rfl
  variation := ⟨@original_piece_suffix_membership, suffixRejected, suffix_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    suffixArena.Law suffixActual suffixRejected suffix_rejected_law
  dependence := by
    intro i
    refine ⟨⟨[Label.L2], 0⟩, 0, 1, ?_⟩
    norm_num [suffixActual, realize, compose, branch, shift]

def original_piece_suffix_membership_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces.original_piece_suffix_membership)
      (type_of% (realize.{0,0,0,0,0} suffixSignature
        (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces.original_piece_suffix_membership_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces.suffixRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨suffixArena⟩
  objectArena := .source ⟨suffixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source suffixArena ⟨suffixRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} suffixSignature
    (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms suffixRegistration
#print axioms original_piece_suffix_membership_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces

namespace Reg.Support.FibonacciOriginalSourceWitness.Source130
noncomputable section

def original_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces.selected_original_piece_tail)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ path => path 0) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.Support.FibonacciOriginalSourceWitness.Source130.original_unit
  realizationName := `Reg.Support.FibonacciOriginalSourceWitness.Source130.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ path => path 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_registration
end
end Reg.Support.FibonacciOriginalSourceWitness.Source130
