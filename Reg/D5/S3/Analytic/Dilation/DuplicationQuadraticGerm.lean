import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Dilation.DuplicationQuadraticGerm
import Reg.Support.SingleDependentReadout

/-! The cosine readout determines every bounded duplication solution with its quadratic germ. -/

namespace Reg.D5.S3.Analytic.Dilation.DuplicationQuadraticGerm

open _root_.D5.S3.Analytic.Dilation.DuplicationQuadraticGerm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Asymptotics
open scoped Topology

noncomputable section

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => Real.cos t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℝ → ℝ} {k : ℝ},
    (∀ t, |f t| ≤ 1) →
    (∀ t, f (2 * t) = 2 * (f t) ^ 2 - 1) →
    ((fun t => f t - (1 - (k ^ 2 / 2) * t ^ 2)) =o[𝓝 0] (fun t => t ^ 2)) →
    ∀ t, f t = R.readout () () (k * t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgerm : (fun t : ℝ => 1 - (1 - (0 ^ 2 / 2) * t ^ 2))
      =o[𝓝 0] (fun t => t ^ 2) := by
    simpa using isLittleO_zero (fun t : ℝ => t ^ 2) (𝓝 0)
  have hh := h (f := fun _ => 1) (k := 0) (by intro t; norm_num)
    (by intro t; norm_num) hgerm 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.pi, ?_⟩
  change Real.cos 0 ≠ Real.cos Real.pi
  norm_num

def family : Registration arena (type_of% @eq_cos_of_quadratic_germ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eq_cos_of_quadratic_germ, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eq_cos_of_quadratic_germ) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.Dilation.DuplicationQuadraticGerm.unit
  realizationName := `Reg.D5.S3.Analytic.Dilation.DuplicationQuadraticGerm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Real.cos t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Analytic.Dilation.DuplicationQuadraticGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Dilation.DuplicationQuadraticGerm
