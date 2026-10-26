import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ReciprocalGammaTuran.Interior
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Defs
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Boundary
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Interior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.ReciprocalGammaTuran.Interior
namespace JointContinuity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ × ℝ × ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ p => turanCoeff (fun _ => 1) p.1 p.2.1 p.2.2 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ p => (Real.log p.1)⁻¹) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := Continuous (fun p => R.readout () () p)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : Continuous (fun x : ℝ => (Real.log x)⁻¹) :=
    h.comp (f := fun x : ℝ => (x, (0, 0))) (by fun_prop)
  exact Real.not_continuousAt_inv_log_one hc.continuousAt
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, (0, 0)), (-(1 / 2), (1 / 2, 1 / 2)), ?_⟩
  change turanCoeff (fun _ => 1) 0 0 0 2 ≠ turanCoeff (fun _ => 1) (-(1 / 2)) (1 / 2) (1 / 2) 2
  have hz : turanCoeff (fun _ => 1) 0 0 0 2 = 0 := by simp [turanCoeff]
  rw [hz]
  exact ne_of_gt (d_two_neg (t := 1 / 2) (by norm_num) (by norm_num))

def family : Registration arena (type_of% @continuous_turanCoeff_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuous_turanCoeff_two, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_turanCoeff_two) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Interior.JointContinuity.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Interior.JointContinuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => turanCoeff (fun _ => 1) p.1 p.2.1 p.2.2 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Interior
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end JointContinuity

namespace Existence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p β => turanCoeff (fun _ => 1) p.1 p.2 β 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∃ μ α β : ℝ,
    0 < μ + α ∧ 0 < μ + β ∧ 0 < α ∧ 0 < β ∧ -1 ≤ μ ∧ R.readout () ⟨μ, α⟩ β < 0
private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨μ, α, β, hμα, hμβ, hα, hβ, hμ, hneg⟩
  exact (lt_irrefl (0 : ℝ)) hneg
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨-(1 / 2), 1 / 2⟩, 0, 1 / 2, ?_⟩
  change turanCoeff (fun _ => 1) (-(1 / 2)) (1 / 2) 0 2 ≠
    turanCoeff (fun _ => 1) (-(1 / 2)) (1 / 2) (1 / 2) 2
  have hz : turanCoeff (fun _ => 1) (-(1 / 2)) (1 / 2) 0 2 = 0 := by
    norm_num [turanCoeff, Finset.sum_range_succ]
    ring
  rw [hz]
  exact ne_of_gt (d_two_neg (t := 1 / 2) (by norm_num) (by norm_num))

def family : Registration arena (type_of% @interior_failure) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨interior_failure, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@interior_failure) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Interior.Existence.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Interior.Existence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p β => turanCoeff (fun _ => 1) p.1 p.2 β 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Interior
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Existence
end Reg.D5.S3.Analytic.ReciprocalGammaTuran.Interior
