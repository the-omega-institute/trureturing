/- SOURCE_ONLY_UNCOMPILED: genuine helper audit attempt using the supplied
Contract, enrollment and raw SourceScope contract. The chosen source operand
is the actual division function partially applied to numerator 1 in the sum.
All original telescope binders, the endpoint correction and zero state remain.
No compiled AST path, source reconstruction or enrollment success is claimed. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail
open scoped BigOperators
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail
open LeanInformationAudit

abbrev inverseSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def inverseActual : Realization inverseSignature :=
  realize inverseSignature (fun _ _ x => 1 / x) (fun e => nomatch e)

def inverseRejected : Realization inverseSignature :=
  realize inverseSignature (fun _ _ _ => 1) (fun e => nomatch e)

def inverse_fourth_partial_le_arena : Arena where
  signature := inverseSignature
  Law r := ∀ {N : ℕ} (hN : 0 < N) (k : ℕ),
    (∑ j ∈ Finset.range k, r.readout () () (((N : ℝ) + (j : ℝ) + 1) ^ 4)) ≤
      1 / (3 * (N : ℝ) ^ 3) - 1 / (3 * ((N : ℝ) + (k : ℝ)) ^ 3)

private theorem inverse_fourth_partial_le_actual_law :
    inverse_fourth_partial_le_arena.Law inverseActual := by
  exact @inverse_fourth_partial_le

private theorem inverse_fourth_partial_le_rejected_law :
    ¬ inverse_fourth_partial_le_arena.Law inverseRejected := by
  intro hall
  have h := hall (N := 1) (by decide) 1
  norm_num [inverse_fourth_partial_le_arena, inverseRejected, realize] at h

private theorem inverseDependence : ObservationalDependence inverseSignature inverseActual := by
  intro i
  refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num [inverseActual, realize]

def inverse_fourth_partial_le_family : Registration inverse_fourth_partial_le_arena
    (type_of% (@inverse_fourth_partial_le)) where
  actual := inverseActual
  bridge := Iff.rfl
  variation := ⟨inverse_fourth_partial_le_actual_law,
    inverseRejected, inverse_fourth_partial_le_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨inverseRejected, ?_, rfl, inverse_fourth_partial_le_rejected_law⟩
      intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := inverseDependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@inverse_fourth_partial_le) (type_of% inverseActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail.inverse_fourth_partial_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail.inverse_fourth_partial_le_family
  realizationSource := none
  generated := false
  arena := .source ⟨inverse_fourth_partial_le_arena⟩
  objectArena := .source ⟨inverse_fourth_partial_le_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverse_fourth_partial_le_arena ⟨inverse_fourth_partial_le_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inverseSignature (fun _ _ x => 1 / x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail
