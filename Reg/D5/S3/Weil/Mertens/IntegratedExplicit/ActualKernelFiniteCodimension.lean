import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension
import Reg.Support.SingleDependentReadout

/-!
UNELABORATED SAME-UNIT OWNER ATTEMPT. No audit or source selection is validated.

The law retains the whole original telescope: arbitrary positive real D,
arbitrary positive target kappa, existential uniform N>=1, universe-polymorphic
finite I selected after N, arbitrary node and complex coefficient functions,
all node bounds and every ordinary moment r<=N. Its result is the conjunction
of coercivity and strict positivity for a nonzero grouped atomic measure. Only
the final real-part observations are intervened on. The actual arithmetic
kernel and prefix norm remain literal, including empty, repeated, unsorted and
zero-energy families.

The constant-minus-one intervention fails for every possible existential N
by the empty family. This witnesses whole-law variation, not merely failure
at one preselected truncation or a finite list of nondegenerate test families.
Actual observational dependence is separately witnessed at complex zero/one.
The existing SingleDependentReadout import supplies the enrolled dependent
family template. This source changes no judge, catalog, tool or CI behavior.
-/

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : ℝ) (hD : 0 < D) (kappa : ℝ) (hkappa : 0 < kappa),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ {I : Type u} [Fintype I]
      (x : I → ℝ) (a : I → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) D) →
      (∀ r : ℕ, r ≤ N → ∑ i, a i * (x i : ℂ) ^ r = 0) →
      kappa * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) ≤
          R.readout () () (∑ i, ∑ j, star (a i) * a j *
            (ActualKernelLocalPositivity.K (x i - x j) : ℂ)) ∧
        ((∃ t : ℝ, (∑ i, if x i = t then a i else 0) ≠ 0) →
          0 < R.readout () () (∑ i, ∑ j, star (a i) * a j *
            (ActualKernelLocalPositivity.K (x i - x j) : ℂ)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨N, _hN, hall⟩ := h 1 (by norm_num) 1 (by norm_num)
  have hb := @hall (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by intro i; cases i.down) (by intro r hr; simp)
  have hbad := hb.1
  norm_num [rejected, realize, «prefix»] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena.{u}
    (type_of% @actual_kernel_finite_codimension_coercivity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_kernel_finite_codimension_coercivity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_kernel_finite_codimension_coercivity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension.actual_kernel_finite_codimension_coercivity.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension.family
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
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Complete source-derived telescope reconstruction: four outer binders;
      -- Exists predicate/body; first result conjunct; six atomic binders;
      -- node and inclusive-moment hypotheses; coercivity RHS; Complex.re.
      -- Source-derived proposal only: binding evaluation has NOT run.
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      -- Second result conjunct: grouped-mass implication and strict RHS.
      -- This is the raw parallel readout path for the actual final source.
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension
end
