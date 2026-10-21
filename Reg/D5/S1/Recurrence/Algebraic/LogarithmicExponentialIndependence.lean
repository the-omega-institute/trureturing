import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.LogarithmicExponentialIndependence
import Reg.Support.DependentFamily

/-!
The generic field-tower lemmas use arbitrary field and algebra instances.
Bundling those instances as data parameters does not reconstruct their raw
theorem telescopes under the current source-selection contract.
-/

noncomputable section

namespace Reg.D5.S1.Recurrence.Algebraic.LogarithmicExponentialIndependence

open _root_.D5.S1.Recurrence.Algebraic.LogarithmicExponentialIndependence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

private def coordinates : Fin 3 → PowerSeries ℚ :=
  ![PowerSeries.X,
    _root_.D5.S1.Recurrence.Algebraic.LogarithmicExponentialSeries.F,
    PowerSeries.derivative
      _root_.D5.S1.Recurrence.Algebraic.LogarithmicExponentialSeries.F]

def actual : Realization signature :=
  realize signature (fun _ _ i => coordinates i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := AlgebraicIndependent ℚ (R.readout () ())

private theorem rejected_bad : ¬ arena.Law rejected := by
  intro h
  change AlgebraicIndependent ℚ (fun _ : Fin 3 => (0 : PowerSeries ℚ)) at h
  exact h.ne_zero 0 rfl

def injection_family : Registration arena (type_of% algebraically_independent) where
  actual := actual
  bridge := by
    constructor <;> exact fun h => h
  variation := ⟨algebraically_independent, rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : Fin 3), (1 : Fin 3), ?_⟩
    intro h
    have he : (0 : Fin 3) = 1 := algebraically_independent.injective h
    exact (by decide : (0 : Fin 3) ≠ 1) he

def injection_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    algebraically_independent (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.LogarithmicExponentialIndependence.algebraically_independent
    "__information_unit"
  realizationName :=
    `Reg.D5.S1.Recurrence.Algebraic.LogarithmicExponentialIndependence.injection_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨injection_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.LogarithmicExponentialIndependence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.LogarithmicExponentialIndependence
