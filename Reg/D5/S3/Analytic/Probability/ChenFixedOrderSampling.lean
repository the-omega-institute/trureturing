import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.ChenFixedOrderSampling
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the sample size and its growth. -/

namespace Reg.D5.S3.Analytic.Probability.ChenFixedOrderSampling

open _root_.ChenFixedOrderSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ m => sampleSize m) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, show sampleSize 0 ≠ sampleSize 1 by decide⟩

namespace FitsStratum

def rejected : Realization signature :=
  realize signature (fun _ _ m => stratumSize m + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ m, r.readout () () m ≤ stratumSize m

private theorem rejected_law : ¬ arena.Law rejected :=
  fun h => Nat.not_succ_le_self (stratumSize 0) (h 0)

def source : Registration arena (type_of% @sampleSize_le_stratumSize) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sampleSize_le_stratumSize, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sampleSize_le_stratumSize) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.ChenFixedOrderSampling.FitsStratum.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.ChenFixedOrderSampling.FitsStratum.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => sampleSize m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.ChenFixedOrderSampling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end FitsStratum

namespace Growth

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := Tendsto (fun m => r.readout () () m) atTop atTop

private theorem rejected_law : ¬ arena.Law rejected :=
  not_tendsto_const_atTop 0 atTop

def source : Registration arena (type_of% @sampleSize_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sampleSize_tendsto, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sampleSize_tendsto) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.ChenFixedOrderSampling.Growth.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.ChenFixedOrderSampling.Growth.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => sampleSize m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.ChenFixedOrderSampling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Growth

end Reg.D5.S3.Analytic.Probability.ChenFixedOrderSampling
