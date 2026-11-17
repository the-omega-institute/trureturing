import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity
import Reg.Support.SingleDependentReadout

noncomputable section
open Set LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q →
    ∀ {α β : ℝ}, 1 < α → α < β → ∀ M : ℕ,
    ∃ κ ∈ Set.Ioo α β, ∃ i j : ℕ, M ≤ i ∧ M ≤ j ∧ 1 ≤ i ∧ 1 ≤ j ∧
      R.readout () () (lcmPowerF κ p i) (lcmPowerF κ q j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨κ, hκ, i, j, hi, hj, hi1, hj1, heq⟩ :=
    h (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
      (α := 2) (β := 3) (by norm_num) (by norm_num) 0
  exact heq

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have hh := congrFun heq 0
  norm_num [actual, realize] at hh

def source_registration : Registration arena (type_of% @collision_parameters_dense) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_parameters_dense, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@collision_parameters_dense) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity.collision_parameters_dense.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity
