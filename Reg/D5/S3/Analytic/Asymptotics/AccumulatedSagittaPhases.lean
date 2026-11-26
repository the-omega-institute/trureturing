import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases

/-! Source-bound registrations for the quartic lower bound of the versine, the accumulated
versine bounds and its three limits.
Each record selects one actual occurrence of its readout in the original statement and
keeps every other clause verbatim. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases
open Filter Topology

noncomputable section
namespace Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases

namespace VersineLower

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.cos x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, x ^ 2 / 2 - x ^ 4 / 24 ≤ 1 - R.readout () () x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  simp only [rejected, realize] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.pi, ?_⟩
  change Real.cos 0 ≠ Real.cos Real.pi
  rw [Real.cos_zero, Real.cos_pi]
  norm_num

def source : Registration arena (type_of% @versine_ge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@versine_ge, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@versine_ge) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases.VersineLower.unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases.VersineLower.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.cos x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end VersineLower

namespace Bounds

abbrev Params := Σ _ : ℝ, Σ _ : ℝ, ℝ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p N => accumulatedSagitta p.1 p.2.1 p.2.2 N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (σ T α : ℝ) (N : ℕ),
    N * (stepAngle σ T α N ^ 2 / 2 - stepAngle σ T α N ^ 4 / 24) ≤ R.readout () ⟨σ, T, α⟩ N ∧
    accumulatedSagitta σ T α N ≤ N * (stepAngle σ T α N ^ 2 / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 1 1 1).1
  simp only [rejected, realize] at hh
  norm_num [stepAngle] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Real.pi, 1, 0⟩, 1, 2, ?_⟩
  change accumulatedSagitta Real.pi 1 0 1 ≠ accumulatedSagitta Real.pi 1 0 2
  norm_num [accumulatedSagitta, stepAngle, Real.cos_pi]

def source : Registration arena (type_of% @accumulated_sagitta_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@accumulated_sagitta_bounds, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@accumulated_sagitta_bounds) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases.Bounds.unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases.Bounds.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p N => accumulatedSagitta p.1 p.2.1 p.2.2 N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Bounds

namespace Phases

abbrev Params := Σ _ : ℝ, ℝ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun _ => ℝ) (fun _ => ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ p α => accumulatedSagitta p.1 p.2 α) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (σ T α : ℝ) (_hT : 0 < T),
    (1 / 2 < α → Tendsto (accumulatedSagitta σ T α) atTop (𝓝 0)) ∧
    (α = 1 / 2 → Tendsto (R.readout () ⟨σ, T⟩ α) atTop (𝓝 (σ ^ 2 * T / 2))) ∧
    (σ ≠ 0 → 0 < α → α < 1 / 2 → Tendsto (accumulatedSagitta σ T α) atTop atTop)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 1 (1 / 2) one_pos).2.1 rfl
  have hone : (1 : ℝ) = 1 ^ 2 * 1 / 2 :=
    tendsto_nhds_unique (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))) hh
  norm_num at hone

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Real.pi, 1⟩, 0, 1, ?_⟩
  intro he
  have h2 := congrFun he 2
  change accumulatedSagitta Real.pi 1 0 2 = accumulatedSagitta Real.pi 1 1 2 at h2
  norm_num [accumulatedSagitta, stepAngle, Real.cos_pi] at h2
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two] at h2
  norm_num at h2

def source : Registration arena (type_of% @accumulated_sagitta_phases) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@accumulated_sagitta_phases, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@accumulated_sagitta_phases) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases.Phases.unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases.Phases.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p α => accumulatedSagitta p.1 p.2 α) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "body", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Phases

end Reg.D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases
