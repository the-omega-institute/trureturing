import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
import Reg.Support.SingleDependentReadout

/-! Author registration of the exact complex square-root family. -/
namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonMultiplicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ m r => spectralRoot m r ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ m r => spectralRoot m r ^ 2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) {r : ℕ}, r ≤ m → R.readout () m r = (squaredValue m r : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (r := 0) (by omega)
  change spectralRoot 1 0 ^ 2 + 1 = (squaredValue 1 0 : ℂ) at hb
  rw [spectralRoot_sq 1 (by omega : 0 ≤ 1)] at hb
  have h01 : (1 : ℂ) = 0 := by linear_combination hb
  exact one_ne_zero h01

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change spectralRoot 1 0 ^ 2 ≠ spectralRoot 1 1 ^ 2
  rw [spectralRoot_sq 1 (by omega : 0 ≤ 1), spectralRoot_sq 1 (le_refl 1)]
  norm_num [squaredValue]

def source : Registration arena (type_of% @spectralRoot_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectralRoot_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectralRoot_sq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m r => spectralRoot m r ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
