import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.CotfasDVGS
import Reg.Support.DependentFamily

/-! Source-bound audit of normalization by the inverse trace. -/

namespace Reg.D5.S3.Quantum.CotfasDVGS.NormalizationIsDensity
open _root_.D5.S3.Quantum.CotfasDVGS (normalization_isDensity)
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe the inverse of the trace in the normalized matrix. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z⁻¹) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (A : Matrix ι ι ℂ),
    A.PosSemidef → A.trace ≠ 0 → IsDensity (R.readout () () A.trace • A)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hd := h (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
    Matrix.PosSemidef.one (by simp [Matrix.trace])
  have ht := hd.2
  simp [rejected, realize, Matrix.trace] at ht

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena.{u}
    (type_of% @normalization_isDensity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalization_isDensity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@normalization_isDensity.{u}) (Realization signature) Unit Unit := {
  unitName := .str `D5.S3.Quantum.CotfasDVGS.normalization_isDensity "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.CotfasDVGS
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.CotfasDVGS.NormalizationIsDensity
