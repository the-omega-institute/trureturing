import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the exact inequality and equality statement. -/

namespace Reg.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
open _root_.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The bound as an observation of the original dimension-dependent data. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => 3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- The full source statement with the first upper-bound occurrence exposed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) →
    (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum ≤
      R.readout () n z) ∧
    ((((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum =
      3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) ↔
        ∀ j, ∃ r : ℝ, z j = (r : ℂ) * z ⟨0, hn⟩)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 (by omega) (fun _ => 1) (by intro j; norm_num)).1
  change (((Polynomial.derivative (P (fun _ : Fin 1 => (1 : ℂ)))).roots.map
    (fun w => ‖w‖⁻¹ ^ 2)).sum ≤ (-1 : ℝ)) at hh
  have hn : 0 ≤ ((Polynomial.derivative (P (fun _ : Fin 1 => (1 : ℂ)))).roots.map
    (fun w => ‖w‖⁻¹ ^ 2)).sum := Multiset.sum_nonneg (by
      intro x hx
      obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hx
      positivity)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ : Fin 1 => (1 : ℂ)), (fun _ => 2), ?_⟩
  norm_num [actual, realize, Fin.sum_univ_one]

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => 3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
    definition := some {
      owner := `D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
      name := `D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Zeros.CriticalPoints.TangZhangOrderMinusTwo
