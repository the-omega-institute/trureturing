import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
import Reg.Support.SingleDependentReadout

/-! Faithful source registration ATTEMPT ONLY, UNCOMPILED.
No declared_validated state or machine binding evidence is asserted.
The readout observes the original complex quadratic form's real part. -/

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- All original binders and the literal original conclusion, except for
observing its real-part operation through the enrolled readout template. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (hlam : 0 < lam)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    2 * lam * (1 - lam ^ 2 * D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) *
        (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) ≤
      R.readout () () (∑ i, ∑ j, star (a i) * a j *
        (Real.exp (-lam * |x i - x j|) : ℂ))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 1 (by norm_num)
    1 (by norm_num) (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down)
    (by intro r hr; simp)
  norm_num [rejected, realize, «prefix»] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena.{u} (type_of% @moment_exponential_prefix_coercivity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_exponential_prefix_coercivity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- Candidate path: twelve original Pi binders, then the inequality's right
operand and its function. This literal path needs later machine verification. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_exponential_prefix_coercivity.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.moment_exponential_prefix_coercivity.audit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
