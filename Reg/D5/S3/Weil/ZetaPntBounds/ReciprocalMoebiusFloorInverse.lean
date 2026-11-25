import D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The finite floor inverse observes the truncated linear target at each cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse

open MeasureTheory LeanInformationAudit
open _root_.D5.S3.Arith.MoebiusLogarithmic (reciprocalSum)
open _root_.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse (floorIntegral_eq)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => max (x - 1) 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P x : ℝ}, 1 ≤ P → 0 ≤ x → x ≤ P →
    (∫ u in (1 : ℝ)..P, reciprocalSum u * (Nat.floor (x / u) : ℝ)) = R.readout () () x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (P := 2) (x := 2) (by norm_num) (by norm_num) le_rfl
  change (∫ u in (1 : ℝ)..2, reciprocalSum u * (Nat.floor (2 / u) : ℝ)) = 0 at hbad
  rw [floorIntegral_eq (by norm_num) (by norm_num) le_rfl] at hbad
  norm_num at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change max ((1 : ℝ) - 1) 0 ≠ max ((2 : ℝ) - 1) 0
  norm_num

def family : Registration arena (type_of% @floorIntegral_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@floorIntegral_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@floorIntegral_eq) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse.floorIntegral_eq.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => max (x - 1) 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
