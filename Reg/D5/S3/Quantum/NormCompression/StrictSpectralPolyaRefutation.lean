import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the real-power identity for squares. -/

namespace Reg.D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation

open _root_.D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a p => (a ^ 2) ^ (p / 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a p : ℝ, R.readout () a p = |a| ^ p

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 1
  change (0 : ℝ) = |(1 : ℝ)| ^ (1 : ℝ) at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨2, 0, 2, ?_⟩
  change ((2 : ℝ) ^ 2) ^ ((0 : ℝ) / 2) ≠ ((2 : ℝ) ^ 2) ^ ((2 : ℝ) / 2)
  norm_num

def source_registration : Registration arena (type_of% @rpow_square_half) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rpow_square_half, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rpow_square_half) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation.source_registration
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
    (realize signature (fun _ a p => (a ^ 2) ^ (p / 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.NormCompression.StrictSpectralPolyaRefutation
