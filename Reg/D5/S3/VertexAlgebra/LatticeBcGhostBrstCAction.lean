import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction

noncomputable section

abbrev signature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Module.End ℂ
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter p =>
    Q parameter.1 parameter.2 * C parameter.1 p +
      C parameter.1 p * Q parameter.1 parameter.2) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : ℤ),
    readout.readout () ⟨D, H⟩ p = -(2 : ℂ)⁻¹ • V D p

def sourceStatement : Prop :=
  ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : ℤ),
    Q D H * C D p + C D p * Q D H = -(2 : ℂ)⁻¹ • V D p

theorem sourceBridge : sourceStatement ↔ arena.Law actual := Iff.rfl

theorem actualPositive : arena.Law actual :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction.c_action

def registrationFromEvidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdependence : ObservationalDependence signature actual) :
    Registration arena (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction.c_action)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualPositive, bad, hbad⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨bad, ?_, (by funext empty; exact nomatch empty), hbad⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := hdependence

def auditFromEvidence (bad : Realization signature) (hbad : ¬ arena.Law bad)
    (hdependence : ObservationalDependence signature actual) :
    Contract.Registration (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction.c_action)
      (Realization signature) (Type) (Unit) where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction.auditFromEvidence
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction.registrationFromEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registrationFromEvidence bad hbad hdependence⟩
  correspondence := ⟨.evidence, .evidence⟩
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameter p =>
    Q parameter.1 parameter.2 * C parameter.1 p +
      C parameter.1 p * Q parameter.1 parameter.2) (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms sourceBridge
#print axioms actualPositive
#print axioms registrationFromEvidence
#print axioms auditFromEvidence

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction
