import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand
import Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand
open _root_.D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
  (neededReserve normalizedPrimeBand)
open _root_.Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand
  (signature actual rejected dependence)

namespace Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand

abbrev largeArena : Arena where
  signature := signature
  Law R := ∀ {z : ℝ}, 10000 ≤ z → 25000 ≤ Real.sqrt (2 * z) →
    neededReserve z < R.readout () () z

private theorem rejected_large : ¬ largeArena.Law rejected := by
  intro h
  have hroot : (25000 : ℝ) ≤ Real.sqrt (2 * (10^9 : ℝ)) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  exact (lt_irrefl _) (h (z := 10^9) (by norm_num) hroot)

def largeFamily : Registration largeArena
    (type_of% (@neededReserve_lt_normalizedPrimeBand_of_sqrt_ge)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neededReserve_lt_normalizedPrimeBand_of_sqrt_ge, rejected, rejected_large⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    largeArena.Law actual rejected rejected_large
  dependence := dependence

def largeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@neededReserve_lt_normalizedPrimeBand_of_sqrt_ge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand_of_sqrt_ge.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand.largeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨largeArena⟩
  objectArena := .source ⟨largeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source largeArena ⟨largeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => normalizedPrimeBand z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand
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

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℝ}, 10000 ≤ z → neededReserve z < R.readout () () z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (lt_irrefl _) (h (z := 10000) (by norm_num))

def family : Registration arena (type_of% (@neededReserve_lt_normalizedPrimeBand)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neededReserve_lt_normalizedPrimeBand, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@neededReserve_lt_normalizedPrimeBand) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand.neededReserve_lt_normalizedPrimeBand.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand
