import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.FiniteMomentCorrelation
import Reg.Support.SingleDependentReadout

/-!
Same-unit dependent-family owner source for the complete uniform statement.
The observed operation is the outer complex norm of the weighted correlation
integral. The prefix energy retains its original norm. Types, coefficients,
nodes, all moments, both positive real parameters and the continuous weight
remain in the original telescope, with the finite type quantified after N.
-/

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Analytic.Interpolation.FiniteMomentCorrelation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Interpolation.FiniteMomentCorrelation

abbrev normSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def normActual : Realization normSignature :=
  realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem normDependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

abbrev correlationArena : Arena where
  signature := normSignature
  Law R := ∀ (D : ℝ) (hD : 0 < D)
    (w : ℝ → ℂ) (hw : ContinuousOn w (Icc (-D) D))
    (ε : ℝ) (hε : 0 < ε),
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ)
        (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
        (hm : ∀ r : ℕ, r < N → ∑ i, a i * (x i : ℂ) ^ r = 0),
        let F := «prefix» x a
        let E : ℝ := ∫ v : ℝ, ‖F v‖ ^ 2
        let C : ℝ → ℂ := fun s => ∫ v : ℝ, star (F (v + s)) * F v
        R.readout () () (∫ s in Icc (-D) D, w s * C s) ≤ ε * E

/-- Constant-one observation fails for every possible N, using an empty family.
Thus the intervention challenges the whole existential law, not a selected N. -/
private theorem correlationRejectedLaw : ¬ correlationArena.{u}.Law normRejected := by
  intro h
  obtain ⟨N, _, hN⟩ := h 1 (by norm_num) (fun _ => 0)
    continuousOn_const 1 (by norm_num)
  have hempty := @hN (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by intro i; cases i.down)
    (by intro r hr; simp)
  norm_num [normRejected, realize, «prefix»] at hempty

/-- Four source obligations: the exact bridge, whole-family variation,
sensitivity of the sole observation, and nonconstant actual observation. -/
def correlationFamily : Registration correlationArena.{u}
    (type_of% @finite_moment_correlation.{u}) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@finite_moment_correlation.{u}, normRejected, correlationRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    correlationArena.Law normActual normRejected correlationRejectedLaw
  dependence := normDependence

/-- The enrolled dependent-family template is supplied by SingleDependentReadout's
existing import of Reg.Support.DependentFamily. No catalog or judge is added. -/
def correlationAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_moment_correlation.{u}) (Realization normSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.FiniteMomentCorrelation.finite_moment_correlation.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.FiniteMomentCorrelation.correlationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨correlationArena⟩
  objectArena := .source ⟨correlationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source correlationArena ⟨correlationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.FiniteMomentCorrelation
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Six outer binders; Exists predicate; second And argument; six atomic
      -- binders; three lets; left side of <=; the norm function operand.
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Interpolation.FiniteMomentCorrelation
