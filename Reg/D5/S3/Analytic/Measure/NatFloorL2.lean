import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Analytic.Measure.NatFloorL2

/-! Source-bound square-summability transfer on the full real sequence family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Measure.NatFloorL2
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Measure.NatFloorL2

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ a x => a (Nat.floor x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℝ) (_ha : Summable (fun n : ℕ => (a (n + 1)) ^ 2)),
    MemLp (fun x : ℝ => R.readout () a x) 2 (volume.restrict (Ioi (1 : ℝ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 0) (by simp)
  change MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioi (1 : ℝ))) at hh
  rw [memLp_const_iff (by norm_num) (by norm_num)] at hh
  simp at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun n => (n : ℝ)), 1, 2, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@memLp_nat_floor_of_summable_sq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@memLp_nat_floor_of_summable_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@memLp_nat_floor_of_summable_sq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Measure.NatFloorL2.memLp_nat_floor_of_summable_sq.audit
  realizationName := `Reg.D5.S3.Analytic.Measure.NatFloorL2.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a x => a (Nat.floor x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Measure.NatFloorL2
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Measure.NatFloorL2
