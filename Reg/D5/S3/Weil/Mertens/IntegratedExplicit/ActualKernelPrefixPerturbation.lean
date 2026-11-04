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


/-- Audit for the explicit finite component-curvature witness.
The witness is selected by D and N; the atom telescope and literal K-P kernel
are unchanged. -/
abbrev finiteCostArena : Arena where
  signature := signature
  Law R := ∀ (D : ℝ) (_hD : 0 < D) (N : ℕ) (_hN : Real.exp D < N),
    0 ≤ _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.finite_curvature_cost D N ∧
    ∀ {I : Type u} [Fintype I]
      (x : I → ℝ) (a : I → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) D) → (∑ i, a i = 0) →
      R.readout () () (∑ i, ∑ j, star (a i) * a j *
        ((ActualKernelLocalPositivity.K (x i - x j) -
          Real.exp (-|x i - x j| / 2) * trivialT |x i - x j| : ℝ) : ℂ)) ≤
        _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.finite_curvature_cost D N *
          (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2)

def finiteCostRejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem finiteCostRejectedLaw : ¬ finiteCostArena.{u}.Law finiteCostRejected := by
  intro h
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp 1)
  obtain ⟨_, hbound⟩ := h 1 (by norm_num) N hN
  have hb := @hbound (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by intro i; cases i.down) (by simp)
  change (1 : ℝ) ≤
    _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.finite_curvature_cost 1 N *
      (∫ v : ℝ, ‖«prefix» (fun _ : ULift.{u} Empty => (0 : ℝ))
        (fun _ => (0 : ℂ)) v‖ ^ 2) at hb
  norm_num [«prefix»] at hb

def finiteCostFamily : Registration finiteCostArena.{u}
    (type_of% @actual_remainder_prefix_bound_with_finite_cost.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_remainder_prefix_bound_with_finite_cost.{u},
    finiteCostRejected, finiteCostRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    finiteCostArena.Law actual finiteCostRejected finiteCostRejectedLaw
  dependence := actual_dependence

noncomputable def finiteCostAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_remainder_prefix_bound_with_finite_cost.{u}) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.actual_remainder_prefix_bound_with_finite_cost
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation "finiteCostFamily"
  realizationSource := none
  generated := false
  arena := .source ⟨finiteCostArena⟩
  objectArena := .source ⟨finiteCostArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteCostArena ⟨finiteCostFamily⟩
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
      path := #["body", "body", "body", "body", "arg", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

open Filter Asymptotics
open scoped Topology

namespace GrowingCorrelation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0),
    R.readout () () (∑ i, ∑ j, star (a i) * a j *
      (Real.exp (|x i - x j| / 2) : ℂ)) = -(∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) -
      (1 / 2) * ∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) *
        (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.GrowingCorrelation.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end GrowingCorrelation


namespace Correlation

/- Correlation source selection remains unfinished under issue #25822. -/

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (N : ℕ) (hN : Real.exp D < N) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0),
    R.readout () () (∑ i, ∑ j, star (a i) * a j *
      ((ActualKernelLocalPositivity.K (x i - x j) -
        Real.exp (-|x i - x j| / 2) * trivialT |x i - x j| : ℝ) : ℂ)) =
    -(Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)) *
      (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) -
    2 * (∑ n ∈ Finset.Icc 2 ⌊Real.exp D⌋₊,
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        (∫ v : ℝ, star («prefix» x a (v + Real.log n)) * «prefix» x a v).re) +
    2 * (∫ s in Icc 0 D, Real.exp (s / 2) *
      (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re) -
    (1 / 2) * (∫ s in Icc 0 D,
      (ActualKernelLocalPositivity.K s - Real.exp (-|s| / 2) * trivialT |s|) *
        (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 0 (by norm_num) 2 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, «prefix»] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena.{u} (type_of% @actual_remainder_correlation_identity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_remainder_correlation_identity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_remainder_correlation_identity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.actual_remainder_correlation_identity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.Correlation.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Correlation


end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
