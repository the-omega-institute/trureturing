import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℝ) (fun _ => ENNReal)

def actual : Realization signature :=
  realize signature (fun _ _ S => volume S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ∅, Set.univ, ?_⟩
  change volume (∅ : Set ℝ) ≠ volume (Set.univ : Set ℝ)
  simp [Real.volume_univ]

namespace Pair

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q →
    {κ : ℝ | 1 < κ ∧ ∃ i j : ℕ,
      1 ≤ i ∧ 1 ≤ j ∧ lcmPowerF κ p i = lcmPowerF κ q j}.Countable ∧
    R.readout () () {κ : ℝ | 1 < κ ∧ ∃ i j : ℕ,
      1 ≤ i ∧ 1 ≤ j ∧ lcmPowerF κ p i = lcmPowerF κ q j} = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
  exact one_ne_zero hh.2

private theorem bridge : (type_of% @collision_parameters_countable_null) ↔
    arena.Law actual := by
  exact Iff.rfl

def family : Registration arena (type_of% @collision_parameters_countable_null) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @collision_parameters_countable_null, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@collision_parameters_countable_null) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable.collision_parameters_countable_null.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable.Pair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => volume S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Pair

namespace All

abbrev arena : Arena where
  signature := signature
  Law R :=
    {κ : ℝ | 1 < κ ∧ ∃ p q i j : ℕ,
      p.Prime ∧ q.Prime ∧ p ≠ q ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j}.Countable ∧
    R.readout () () {κ : ℝ | 1 < κ ∧ ∃ p q i j : ℕ,
      p.Prime ∧ q.Prime ∧ p ≠ q ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j} = 0 ∧
    (∀ᵐ κ : ℝ ∂volume, 1 < κ → ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Disjoint ((fun i : ℕ => lcmPowerF κ p i) '' {i : ℕ | 1 ≤ i})
        ((fun j : ℕ => lcmPowerF κ q j) '' {j : ℕ | 1 ≤ j}))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact one_ne_zero h.2.1

private theorem bridge : (type_of% @all_collision_parameters_countable_null) ↔
    arena.Law actual := by
  exact Iff.rfl

def family : Registration arena (type_of% @all_collision_parameters_countable_null) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @all_collision_parameters_countable_null, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@all_collision_parameters_countable_null) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable.all_collision_parameters_countable_null.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable.All.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => volume S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end All
end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCountable
