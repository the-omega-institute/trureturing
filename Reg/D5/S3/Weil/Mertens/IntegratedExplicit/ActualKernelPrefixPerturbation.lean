import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
import Reg.Support.SingleDependentReadout

/-!
The original theorem's whole telescope is retained: D, positivity of D,
existential M, its nonnegativity, arbitrary universe-polymorphic finite I,
the whole node and coefficient functions, all node bounds, and zero total mass.
There is no added high-moment hypothesis and no finite list of test atom families.

Only the outer norm readout is intervened on. The inner prefix norm and the
literal K-P kernel are unchanged in the reconstructed source law. The actual
readout is the ordinary complex norm, not an unconstrained truth-valued witness.
The constant-one intervention fails on the empty atom type for every candidate M.
Sensitivity is for the entire readout family. Actual observational dependence
is witnessed separately at complex inputs zero and one.

The source selection locates precisely the outer complex norm.
-/

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : ℝ) (_hD : 0 < D),
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {I : Type u} [Fintype I]
      (x : I → ℝ) (a : I → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) D) → (∑ i, a i = 0) →
      R.readout () () (∑ i, ∑ j, star (a i) * a j *
        ((ActualKernelLocalPositivity.K (x i - x j) -
          Real.exp (-|x i - x j| / 2) * trivialT |x i - x j| : ℝ) : ℂ)) ≤
        M * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨M, hM, hbound⟩ := h 1 (by norm_num)
  have hb := @hbound (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by intro i; cases i.down) (by simp)
  change (1 : ℝ) ≤ M * (∫ v : ℝ,
    ‖«prefix» (fun _ : ULift.{u} Empty => (0 : ℝ)) (fun _ => (0 : ℂ)) v‖ ^ 2) at hb
  norm_num [«prefix»] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def family : Registration arena.{u}
    (type_of% @actual_remainder_prefix_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_remainder_prefix_bound.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/- The imported SingleDependentReadout imports the existing typed enrollment of
DependentFamily.realize. No new enrollment, catalog or judgment rule is added.
The complete kernel proof obligations reside in `family`; the four-slot contract
keeps realization, lawful template readout, original source selection and residual
continuation together, using the same owner pattern as AtomicPrefixEnergy. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_remainder_prefix_bound.{u}) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.actual_remainder_prefix_bound
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
