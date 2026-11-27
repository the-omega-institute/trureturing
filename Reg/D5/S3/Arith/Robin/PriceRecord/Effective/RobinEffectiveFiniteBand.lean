import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.Effective
  (neededReserve_lt_normalizedPrimeBand_of_sqrt_le)
open _root_.D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
  (D neededReserve normalizedPrimeBand)

namespace Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => normalizedPrimeBand z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z => neededReserve z) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 10000, ?_⟩
  change normalizedPrimeBand 0 ≠ normalizedPrimeBand 10000
  have hzero : normalizedPrimeBand 0 = 0 := by simp [normalizedPrimeBand, D]
  have hroot : Real.sqrt (2 * (10000 : ℝ)) ≤ 25000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hpos : 0 < neededReserve (10000 : ℝ) := by
    unfold neededReserve
    have hlog : 0 < Real.log (10000 : ℝ) := Real.log_pos (by norm_num)
    positivity
  rw [hzero]
  exact (hpos.trans (neededReserve_lt_normalizedPrimeBand_of_sqrt_le (by norm_num) hroot)).ne

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℝ}, 10000 ≤ z → Real.sqrt (2 * z) ≤ 25000 →
    neededReserve z < R.readout () () z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hroot : Real.sqrt (2 * (10000 : ℝ)) ≤ 25000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  exact (lt_irrefl _) (h (z := 10000) (by norm_num) hroot)

def family : Registration arena (type_of% (@neededReserve_lt_normalizedPrimeBand_of_sqrt_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neededReserve_lt_normalizedPrimeBand_of_sqrt_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@neededReserve_lt_normalizedPrimeBand_of_sqrt_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.Effective.neededReserve_lt_normalizedPrimeBand_of_sqrt_le.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => normalizedPrimeBand z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand
