import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
import Reg.Support.DependentFamily

/-! Source-bound audit of symmetric SATWAP attainment through the Bell value. -/

namespace Reg.D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation

open _root_.D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the SATWAP Bell value in the original dimension and bipartite state. -/
abbrev signature : Signature where
  Params := ℕ
  State d := EuclideanSpace ℂ (Fin d × Fin d)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d ψ => satwapValue d ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep normalization, swap symmetry, the reduced state, and exact Bell attainment. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, 2 ≤ d →
    ∃ ψ : EuclideanSpace ℂ (Fin d × Fin d),
      ‖ψ‖ = 1 ∧
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm (Fin d) (Fin d)) ψ = ψ ∧
      reducedState ψ = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
      R.readout () d ψ = 2 * ((d : ℂ) - 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ψ, _, _, _, hbell⟩ := h 2 (by norm_num)
  change (0 : ℂ) = 2 * ((2 : ℂ) - 1) at hbell
  norm_num at hbell

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨ψ, _, _, _, hbell⟩ := result 2 (by norm_num)
  refine ⟨2, 0, ψ, ?_⟩
  change satwapValue 2 0 ≠ satwapValue 2 ψ
  have hzero : satwapValue 2 0 = 0 := by
    simp [satwapValue, correlator, prob]
  rw [hzero, hbell]
  norm_num

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
      (@_root_.D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ d ψ => satwapValue d ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
      name := `D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
