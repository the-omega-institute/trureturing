import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
import Reg.Support.SingleDependentReadout

/-! Source-bound coefficient observations with the complete parameter telescopes. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
noncomputable section
set_option autoImplicit false

namespace Positive

abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ κ x => coefficient κ x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ x : ℝ}, 1 < κ → 1 < x → 0 < R.readout () κ x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h (κ := 2) (x := 2) (by norm_num) (by norm_num))

def family : Registration arena (type_of% @coefficient_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 1, 2, ?_⟩
    change coefficient 2 1 ≠ coefficient 2 2
    have hp := coefficient_pos (κ := 2) (x := 2) (by norm_num) (by norm_num)
    simpa only [coefficient, sub_self, zero_mul, zero_div, Real.one_rpow] using hp.ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_pos) (Realization signature) Unit Unit where
  unitName := `LcmPowerCollisionCoefficient.coefficient_pos.unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ κ x => coefficient κ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positive

namespace Ratio

abbrev signature := Reg.Support.SingleDependentReadout.signature (ℝ × ℝ)
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ pq κ => Real.log (coefficient κ pq.1 / coefficient κ pq.2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℝ}, 1 < p → p < q → StrictMonoOn (R.readout () (p, q)) (Set.Ioi 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 2) (q := 3) (by norm_num) (by norm_num)
    (a := 2) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hh

def family : Registration arena (type_of% @log_coefficient_ratio_strictMono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_coefficient_ratio_strictMono, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(2, 3), 2, 3, ?_⟩
    exact (log_coefficient_ratio_strictMono (p := 2) (q := 3) (by norm_num) (by norm_num)
      (a := 2) (b := 3) (by norm_num) (by norm_num) (by norm_num)).ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_coefficient_ratio_strictMono) (Realization signature) Unit Unit where
  unitName := `LcmPowerCollisionCoefficient.log_coefficient_ratio_strictMono.unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient.Ratio.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ pq κ => Real.log (coefficient κ pq.1 / coefficient κ pq.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Ratio
end
end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
