import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
import Reg.Support.SingleDependentReadout

/-! Whole-family variation of the exact rational arithmetic predicates. -/

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel

open _root_.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
open _root_.D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev arithmeticSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries ℚ) (fun _ => Prop)

def arithmeticActual : Realization arithmeticSignature :=
  realize arithmeticSignature
    (fun _ _ F => IsSource F)
    (fun e => nomatch e)

def arithmeticRejected : Realization arithmeticSignature :=
  realize arithmeticSignature (fun _ _ _ => True) (fun e => nomatch e)

private theorem arithmetic_dependence :
    ObservationalDependence arithmeticSignature arithmeticActual := by
  intro i
  obtain ⟨F, hF, _⟩ := triangular_exists_unique
    (fun n => (n : ℚ) ^ 2) (fun n => (n : ℚ) ^ 2)
    (fun n hn => pow_ne_zero _ (by exact_mod_cast (show n ≠ 0 by omega)))
  have hno : ¬ IsSource (1 : PowerSeries ℚ) := by
    intro h
    simpa using h.1
  refine ⟨(), F, 1, ?_⟩
  change IsSource F ≠ IsSource (1 : PowerSeries ℚ)
  intro he
  exact hno (he ▸ hF)

abbrev obstructionArena : Arena where
  signature := arithmeticSignature
  Law R := ∀ (F : PowerSeries ℚ), R.readout () () F → ∀ n : ℕ,
    (∀ j < n, ∃ z : ℤ, coeff j F = (z : ℚ)) →
    (¬ ∃ z : ℤ, coeff n F = (z : ℚ)) →
    2 ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p < n ∧ ¬ p ∣ n ∧ p ∣ (coeff n F).den

private theorem obstruction_rejected : ¬ obstructionArena.Law arithmeticRejected := by
  intro h
  have hb : ¬ ∃ z : ℤ, coeff 0 (C (1 / 2 : ℚ)) = (z : ℚ) := by
    rintro ⟨z, hz⟩
    have hd := congrArg Rat.den hz
    norm_num at hd
  have hh := h (C (1 / 2)) True.intro 0 (by intro j hj; omega) hb
  omega

def obstructionFamily : Registration obstructionArena (type_of% source_denominator_obstruction) where
  actual := arithmeticActual
  bridge := by simp [arithmeticActual, realize]
  variation := ⟨by simpa [arithmeticActual, realize] using source_denominator_obstruction,
    arithmeticRejected, obstruction_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    obstructionArena.Law arithmeticActual arithmeticRejected obstruction_rejected
  dependence := arithmetic_dependence

abbrev localArena : Arena where
  signature := arithmeticSignature
  Law R := ∀ (F : PowerSeries ℚ), R.readout () () F → ∀ n : ℕ, 2 ≤ n →
    ∀ p : ℕ, p.Prime → p ∣ n →
      (∀ j < n, IsRIntegralRat p (coeff j F)) →
      IsRIntegralRat p (coeff n F / (n : ℚ))

private theorem local_rejected : ¬ localArena.Law arithmeticRejected := by
  intro h
  have hpref : ∀ j < 2, IsRIntegralRat 2 (coeff j ((X : PowerSeries ℚ) ^ 2)) := by
    intro j hj
    simp [coeff_X_pow, show j ≠ 2 by omega, IsRIntegralRat]
  have hh := h (X ^ 2) True.intro 2 (by omega) 2 (by decide) (by simp) hpref
  norm_num [IsRIntegralRat] at hh

def localFamily : Registration localArena (type_of% source_local_quotient) where
  actual := arithmeticActual
  bridge := by simp [arithmeticActual, realize]
  variation := ⟨by simpa [arithmeticActual, realize] using source_local_quotient,
    arithmeticRejected, local_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    localArena.Law arithmeticActual arithmeticRejected local_rejected
  dependence := arithmetic_dependence

abbrev divisibilityArena : Arena where
  signature := arithmeticSignature
  Law R := ∀ (F : PowerSeries ℚ), R.readout () () F →
    (∀ r : ℕ, ∃ z : ℤ, coeff r F = (z : ℚ)) →
    ∀ n : ℕ, 1 ≤ n → ∃ q : ℤ, coeff n F = (n : ℚ) * (q : ℚ)

private theorem divisibility_rejected : ¬ divisibilityArena.Law arithmeticRejected := by
  intro h
  have hints : ∀ r : ℕ, ∃ z : ℤ, coeff r ((X : PowerSeries ℚ) ^ 2) = (z : ℚ) := by
    intro r
    by_cases hr : r = 2
    · subst r; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [coeff_X_pow, hr]⟩
  obtain ⟨q, hq⟩ := h (X ^ 2) True.intro hints 2 (by omega)
  have he : (1 / 2 : ℚ) = (q : ℚ) := by
    norm_num at hq
    linarith
  have hd := congrArg Rat.den he
  norm_num at hd

def divisibilityFamily : Registration divisibilityArena (type_of% source_divisible_of_integral) where
  actual := arithmeticActual
  bridge := by simp [arithmeticActual, realize]
  variation := ⟨by simpa [arithmeticActual, realize] using source_divisible_of_integral,
    arithmeticRejected, divisibility_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    divisibilityArena.Law arithmeticActual arithmeticRejected divisibility_rejected
  dependence := arithmetic_dependence

def obstructionAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    source_denominator_obstruction (Realization arithmeticSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.source_denominator_obstruction.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.obstructionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨obstructionArena⟩
  objectArena := .source ⟨obstructionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source obstructionArena ⟨obstructionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arithmeticSignature arithmeticActual.readout arithmeticActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def localAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    source_local_quotient (Realization arithmeticSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.source_local_quotient.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.localFamily
  realizationSource := none
  generated := false
  arena := .source ⟨localArena⟩
  objectArena := .source ⟨localArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source localArena ⟨localFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arithmeticSignature arithmeticActual.readout arithmeticActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def divisibilityAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    source_divisible_of_integral (Realization arithmeticSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.source_divisible_of_integral.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.divisibilityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨divisibilityArena⟩
  objectArena := .source ⟨divisibilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source divisibilityArena ⟨divisibilityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arithmeticSignature arithmeticActual.readout arithmeticActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev integralArena : Arena where
  signature := arithmeticSignature
  Law R := ∀ (F : PowerSeries ℚ), R.readout () () F →
    (∀ r : ℕ, ∃ z : ℤ, coeff r F = (z : ℚ)) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ q : ℤ, coeff n F = (n : ℚ) * (q : ℚ)

private theorem integral_rejected : ¬ integralArena.Law arithmeticRejected := by
  intro h
  obtain ⟨z, hz⟩ := (h (C (1 / 2)) True.intro).1 0
  have hd := congrArg Rat.den hz
  norm_num at hd

def integralFamily : Registration integralArena (type_of% source_integral_and_divisible) where
  actual := arithmeticActual
  bridge := by simp [arithmeticActual, realize]
  variation := ⟨by simpa [arithmeticActual, realize] using source_integral_and_divisible,
    arithmeticRejected, integral_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integralArena.Law arithmeticActual arithmeticRejected integral_rejected
  dependence := arithmetic_dependence

/-- The full source telescope is retained; scoped observation reconstruction is unresolved. -/
def integralAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    source_integral_and_divisible (Realization arithmeticSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.source_integral_and_divisible.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel.integralFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integralArena⟩
  objectArena := .source ⟨integralArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integralArena ⟨integralFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arithmeticSignature arithmeticActual.readout arithmeticActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
