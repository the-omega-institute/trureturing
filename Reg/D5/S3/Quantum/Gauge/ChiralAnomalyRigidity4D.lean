import D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => sinSqFixed ℚ n) (fun e => nomatch e)

def zeroCurve : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    traceWeakSq ℚ n / (traceWeakSq ℚ n + traceYSq n spectralHypercharges) = R.readout () () n

private theorem zero_curve_fails : ¬ arena.Law zeroCurve := by
  intro h
  have hh := h 3
  change traceWeakSq ℚ 3 / (traceWeakSq ℚ 3 + traceYSq 3 spectralHypercharges) = 0 at hh
  rw [fixed_charge_weak_mixing] at hh
  norm_num [sinSqFixed] at hh

def familyRegistration : Registration arena (type_of% (@fixed_charge_weak_mixing)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_charge_weak_mixing, zeroCurve, zero_curve_fails⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨zeroCurve, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, zero_curve_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 3, ?_⟩
    change sinSqFixed ℚ 0 ≠ sinSqFixed ℚ 3
    norm_num [sinSqFixed]

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_charge_weak_mixing) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D.fixed_charge_weak_mixing.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence
    ⟨(show Nonempty (Realization signature) from ⟨actual⟩)⟩ trivial
  readout := some (realize signature (fun _ _ n => sinSqFixed ℚ n) (fun e => nomatch e))
  variation := .evidence ⟨familyRegistration.variation⟩ trivial
  sensitivity := .evidence ⟨familyRegistration.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D
