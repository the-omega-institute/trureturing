import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
import Reg.Support.SingleDependentReadout

/-! Source registration for the nonzero real-root count of the polygon Jacobian. -/

namespace Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
open _root_.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature
    (fun _ _ m => {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ m =>
    {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 3 ≤ m →
    (∀ x : ℝ, (jacobian (2 * m)).charpoly.IsRoot x →
      (jacobian (2 * m)).charpoly.IsRoot (-x)) ∧
      R.readout () () m = 2 * (m - 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 3 (by omega)).2
  have ha := (result 3 (by omega)).2
  change {x : ℝ | x ≠ 0 ∧ (jacobian (2 * 3)).charpoly.IsRoot x}.ncard + 1 = _ at hb
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 3, 4, ?_⟩
  change {x : ℝ | x ≠ 0 ∧ (jacobian (2 * 3)).charpoly.IsRoot x}.ncard ≠
    {x : ℝ | x ≠ 0 ∧ (jacobian (2 * 4)).charpoly.IsRoot x}.ncard
  rw [(result 3 (by omega)).2, (result 4 (by omega)).2]
  norm_num

def source : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.unit
  realizationName := `Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ m => {x : ℝ | x ≠ 0 ∧ (jacobian (2 * m)).charpoly.IsRoot x}.ncard)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
    definition := some {
      owner := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
      name := `D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum
