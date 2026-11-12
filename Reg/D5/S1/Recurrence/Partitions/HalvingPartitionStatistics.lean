import D5.S1.Recurrence.Partitions.HalvingPartitionStatistics
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
namespace Reg.D5.S1.Recurrence.Partitions.HalvingPartitionStatistics
open _root_.D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private theorem threshold_small (m : ℕ) (hm : m < 4) : thresholdCount m = 0 := by
  by_contra hz
  have h := (threshold_iff_le_count m 1).mpr ⟨by decide, by omega⟩
  norm_num at h
  omega

private theorem threshold_four : thresholdCount 4 = 1 := by
  have hlo := ((threshold_iff_le_count 4 1).mp (by norm_num)).2
  have hhi : ¬ 2 ≤ thresholdCount 4 := by
    intro hh
    have hx := (threshold_iff_le_count 4 2).mpr ⟨by decide, hh⟩
    norm_num at hx
  omega

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

namespace Mean
abbrev actual : Realization signature :=
  realize signature (fun _ _ n => meanLength n) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ n => meanLength n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law W := ∀ (m : ℕ) (_hm : 2 ≤ m),
    W.readout () () (2 ^ m + 1) = m + 1 - (thresholdCount m : ℚ) / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h 2 (by decide)
  have ht := meanLength_dyadic 2 (by decide)
  change meanLength (2 ^ 2 + 1) + 1 = _ at hs
  rw [ht] at hs
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2 ^ 2 + 1, 2 ^ 3 + 1, ?_⟩
  change meanLength (2 ^ 2 + 1) ≠ meanLength (2 ^ 3 + 1)
  rw [meanLength_dyadic 2 (by decide), meanLength_dyadic 3 (by decide)]
  norm_num [threshold_small 2 (by decide), threshold_small 3 (by decide),
    threshold_four]

def family : Registration arena (type_of% (@meanLength_dyadic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨meanLength_dyadic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@meanLength_dyadic) (Realization signature) Type Unit where
  unitName := `D5.S1.Recurrence.Partitions.HalvingPartitionStatistics.meanLength_dyadic.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Partitions.HalvingPartitionStatistics.Mean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => meanLength n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Partitions.HalvingPartitionStatistics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Mean

namespace Variance
abbrev actual : Realization signature :=
  realize signature (fun _ _ n => varianceLength n) (fun e => nomatch e)
abbrev rejected : Realization signature :=
  realize signature (fun _ _ n => varianceLength n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law W := ∀ (m : ℕ) (_hm : 2 ≤ m),
    W.readout () () (2 ^ m + 1) = (((thresholdCount m : ℚ) + 3) ^ 2 - 1) / 12

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h 2 (by decide)
  have ht := varianceLength_dyadic 2 (by decide)
  change varianceLength (2 ^ 2 + 1) + 1 = _ at hs
  rw [ht] at hs
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2 ^ 2 + 1, 2 ^ 4 + 1, ?_⟩
  change varianceLength (2 ^ 2 + 1) ≠ varianceLength (2 ^ 4 + 1)
  rw [varianceLength_dyadic 2 (by decide), varianceLength_dyadic 4 (by decide)]
  norm_num [threshold_small 2 (by decide), threshold_small 3 (by decide),
    threshold_four]

def family : Registration arena (type_of% (@varianceLength_dyadic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨varianceLength_dyadic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@varianceLength_dyadic) (Realization signature) Type Unit where
  unitName := `D5.S1.Recurrence.Partitions.HalvingPartitionStatistics.varianceLength_dyadic.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Partitions.HalvingPartitionStatistics.Variance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => varianceLength n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Partitions.HalvingPartitionStatistics
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Variance

end Reg.D5.S1.Recurrence.Partitions.HalvingPartitionStatistics
