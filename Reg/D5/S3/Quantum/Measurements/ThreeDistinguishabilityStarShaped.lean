import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic (infeasibleWeights)
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity
  (one_zero_feasible infeasible_not_inRegion)
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation (InRegion)
open _root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped
  (inRegion_uniform_interpolation)

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 4 → ℝ)
    (fun _ => ℝ) (fun _ => Fin 4 → ℝ)

/-- Read the interpolated law at the given segment parameter. -/
def actual : Realization signature :=
  realize signature (fun _ p s i => (1 - s) * (1 / 4 : ℝ) + s * p i) (fun e => nomatch e)

/-- Replace the interpolated outcome law by a fixed excluded law. -/
def fixedExcludedLaw : Realization signature :=
  realize signature (fun _ _ _ => infeasibleWeights) (fun e => nomatch e)

/-- Retain the starting law's membership and both interpolation bounds. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Fin 4 → ℝ), InRegion p → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    InRegion (R.readout () p s)

private abbrev corner : Fin 4 → ℝ := ![0, 1 / 3, 1 / 3, 1 / 3]

private theorem fixedExcludedLaw_fails : ¬ arena.Law fixedExcludedLaw := by
  intro h
  exact infeasible_not_inRegion (h corner one_zero_feasible 0 le_rfl zero_le_one)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨corner, 0, 1, ?_⟩
  intro heq
  have hzero := congrFun heq 0
  change (1 - 0) * (1 / 4 : ℝ) + 0 * corner 0 =
    (1 - 1) * (1 / 4 : ℝ) + 1 * corner 0 at hzero
  norm_num [corner] at hzero

def source_registration : Registration arena (type_of% @inRegion_uniform_interpolation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨inRegion_uniform_interpolation, fixedExcludedLaw, fixedExcludedLaw_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual
    fixedExcludedLaw fixedExcludedLaw_fails
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped.inRegion_uniform_interpolation)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped.unit
  realizationName := `Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s i => (1 - s) * (1 / 4 : ℝ) + s * p i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Measurements.ThreeDistinguishabilityStarShaped
