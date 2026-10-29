import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.ExponentialHankelPositivity
import Reg.Support.SingleDependentReadout

/-! The law retains the arbitrary cutoff, the original continuous signed L1
source, every moment, every real coefficient vector, the exact integral
identity, and both directions of positivity detection. The selected readout
is the original density in the pointwise positivity clause. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Matrix
open scoped Topology BigOperators
open _root_.D5.S3.Analytic.Laplace.ExponentialHankelPositivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.ExponentialHankelPositivity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ g => g) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

set_option maxHeartbeats 1000000 in
def arena : Arena where
  signature := signature
  Law r := ∀ (U : ℝ) (g : ℝ → ℝ)
    (_hc : ContinuousOn g (Ioi U)) (_hg : IntegrableOn g (Ioi U)),
    (∀ k : ℕ, IntegrableOn
      (fun u => g u * Real.exp (-(k : ℝ) * (u - U))) (Ioi U)) ∧
    (∀ (N : ℕ) (c : Fin (N + 1) → ℝ),
      IntegrableOn (fun u => g u *
        (∑ i, c i * Real.exp (-(i.val : ℝ) * (u - U))) ^ 2) (Ioi U) ∧
      star c ⬝ᵥ (exponentialHankel U g N *ᵥ c) =
        ∫ u in Ioi U, g u *
          (∑ i, c i * Real.exp (-(i.val : ℝ) * (u - U))) ^ 2) ∧
    ((∀ u ∈ Ioi U, 0 ≤ r.readout () () g u) ↔
      ∀ N : ℕ, (exponentialHankel U g N).PosSemidef)

private theorem source_reconstruction :
    (type_of% @exponential_hankel_positivity) ↔ arena.Law actual := Iff.rfl

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hzero := exponential_hankel_positivity 0 (fun _ => 0)
    continuousOn_const (integrable_zero _ _ _)
  have hpsd := hzero.2.2.mp (by intro u hu; exact le_rfl)
  have hbad := (h 0 (fun _ => 0) continuousOn_const (integrable_zero _ _ _)).2.2.mpr hpsd
  have hneg := hbad 1 (by norm_num)
  norm_num [rejected, realize] at hneg

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun u : ℝ => -Real.exp (-u)), ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def evidence : Registration arena (type_of% @exponential_hankel_positivity) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@exponential_hankel_positivity, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exponential_hankel_positivity) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.Laplace.ExponentialHankelPositivity.exponential_hankel_positivity.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.ExponentialHankelPositivity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ g => g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.ExponentialHankelPositivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg",
        "body", "body", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms audit

end Reg.D5.S3.Analytic.Laplace.ExponentialHankelPositivity
