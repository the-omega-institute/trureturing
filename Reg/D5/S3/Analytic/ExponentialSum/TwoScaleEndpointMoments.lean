import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Source-faithful mass-readout registration for the uniform endpoint moment theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
open _root_.TwoScaleEndpointMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Set
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ × ℝ × ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q p =>
    ∫ x : ℝ in Ioi q.2.2, twoScaleEndpoint q.1 q.2.1 q.2.2 p x ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b endpoint p : ℝ) (_hp : 0 < p) (k : ℕ),
    IntegrableOn (fun x : ℝ => (x - endpoint) ^ k *
      twoScaleEndpoint a b endpoint p x ^ 2) (Ioi endpoint) ∧
      (a ^ 2 + b ^ 2) / (54 * p) ≤ R.readout () (a, b, endpoint) p ∧
      (∫ x : ℝ in Ioi endpoint, (x - endpoint) ^ k *
        twoScaleEndpoint a b endpoint p x ^ 2) ≤
        (54 * (k.factorial : ℝ) / p ^ k) *
          (∫ x : ℝ in Ioi endpoint, twoScaleEndpoint a b endpoint p x ^ 2)

private theorem source_reconstruction :
    (type_of% (@two_scale_endpoint_moment_bound)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm := (h 1 0 0 1 (by norm_num) 0).2.1
  norm_num [rejected, realize] at hm

private theorem rate_mass (p : ℝ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0, twoScaleEndpoint 1 0 0 p x ^ 2) = 1 / (2 * p) := by
  have he (x : ℝ) : twoScaleEndpoint 1 0 0 p x ^ 2 = Real.exp (-(2 * p) * x) := by
    simp only [twoScaleEndpoint, twoScaleShape, one_mul, zero_mul, add_zero,
      sub_zero, pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = ∫ x : ℝ in Ioi 0, Real.exp (-(2 * p) * x) :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by
      simpa using integral_exp_mul_Ioi (a := -(2 * p)) (by linarith) 0

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1, 0, 0), 1, 2, ?_⟩
  change (∫ x : ℝ in Ioi 0, twoScaleEndpoint 1 0 0 1 x ^ 2) ≠
    ∫ x : ℝ in Ioi 0, twoScaleEndpoint 1 0 0 2 x ^ 2
  rw [rate_mass 1 (by norm_num), rate_mass 2 (by norm_num)]
  norm_num

def family : Registration arena (type_of% (@two_scale_endpoint_moment_bound)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨two_scale_endpoint_moment_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@two_scale_endpoint_moment_bound) (Realization signature) Unit Unit where
  unitName := `TwoScaleEndpointMoments.two_scale_endpoint_moment_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q p =>
    ∫ x : ℝ in Ioi q.2.2, twoScaleEndpoint q.1 q.2.1 q.2.2 p x ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
