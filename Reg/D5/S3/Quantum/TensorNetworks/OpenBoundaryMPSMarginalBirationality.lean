import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
import Reg.Support.DependentFamily

/-! Source-bound audit of the vanishing-ideal coordinate in the birationality settlement. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality

open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Evaluate a polynomial-ideal family at the original chain length. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ n : ℕ, Ideal (MvPolynomial (Fin n → Fin 2) ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Ideal (MvPolynomial (Fin n → Fin 2) ℂ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n I => I n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

/-- Preserve all lengths, positions, hypotheses, prime ideals and rational inverses. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n a : ℕ, 4 ≤ n → ∀ h : a + 3 ≤ n,
    (R.readout () n vanishingPolys).IsPrime ∧
      (vanishingPolys 3).IsPrime ∧ IsBirationalVia n a h

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 4 0 (by norm_num) (by norm_num)).1.ne_top rfl

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => ⊥), (fun _ => ⊤), ?_⟩
  exact bot_ne_top

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n I => I n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
    definition := some {
      owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
      name := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.result
#print _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
