import D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound normalization of the scalar exponential at one. -/

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel

open _root_.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev oneSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries ℚ) (fun _ => PowerSeries ℚ)

def oneActual : Realization oneSignature :=
  realize oneSignature (fun _ _ F => expSeries 1 F) (fun e => nomatch e)

def oneVariation : Realization oneSignature :=
  realize oneSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev oneArena : Arena where
  signature := oneSignature
  Law R := ∀ F : PowerSeries ℚ, R.readout () () F = (exp ℚ).subst F

private theorem oneVariation_fails : ¬ oneArena.Law oneVariation := by
  intro h
  have he : constantCoeff (0 : PowerSeries ℚ) = constantCoeff (expSeries 1 0) :=
    congrArg constantCoeff ((h 0).trans (expSeries_one 0).symm)
  rw [map_zero, expSeries_zero 1 (map_zero _)] at he
  exact zero_ne_one he

def oneFamily : Registration oneArena (type_of% expSeries_one) where
  actual := oneActual
  bridge := Iff.rfl
  variation := ⟨expSeries_one, oneVariation, oneVariation_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    oneArena.Law oneActual oneVariation oneVariation_fails
  dependence := by
    intro i
    refine ⟨(), 0, X, ?_⟩
    intro h
    have he : (exp ℚ).subst (0 : PowerSeries ℚ) = (exp ℚ).subst (X : PowerSeries ℚ) := by
      simpa only [oneActual, realize, expSeries_one] using h
    have hX := PowerSeries.X_subst (exp ℚ)
    rw [hX] at he
    have hc := congrArg (fun F : PowerSeries ℚ => coeff 1 F) he
    simp [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.coeff_exp] at hc

def oneAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    expSeries_one (Realization oneSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.expSeries_one.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.oneFamily
  realizationSource := none
  generated := false
  arena := .source ⟨oneArena⟩
  objectArena := .source ⟨oneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source oneArena ⟨oneFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize oneSignature (fun _ _ F => expSeries 1 F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
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
  options := #[]

end

end Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
