import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelFiniteCompleteObstruction FourthSegmentStoppedLaw NativeBorelCommonFlow NativeBorelEndpointIdentification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped ENNReal

abbrev familySignature : Signature where
  Params := ActivePhase
  State _ := CurveParameter
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := RegularDescriptor s
  Anchor := Empty
  finiteAnchor := inferInstance

def familyActual : Realization familySignature :=
  realize _ (fun _ s t => curveDescriptor s t) (fun e => nomatch e)

def familyArena : Arena where
  signature := familySignature
  Law R := (∀ s, Measurable (fun t => R.readout 0 s t)) ∧
    ∀ t : CurveParameter,
      (∀ n b, (law (R.readout 0 .p t)).real {pAtom n b} =
        (if b=0 then curveU t else curveG t)*(t:ℝ)^n) ∧
      (∀ n b, (law (R.readout 0 .beta t)).real {betaAtom n b} =
        curveV t*((if b=0 then curveU t else curveG t)*(t:ℝ)^n)) ∧
      (∀ s, law (R.readout 0 s t) Set.univ = 1 ∧
        law (R.readout 0 s t) {infinity s} = 0 ∧
        law (R.readout 0 s t) (tailSet s 0) =
          (if s=.p then 1 else ENNReal.ofReal (curveV t)) ∧
        EndpointBox (R.readout 0 s t)) ∧
      residualB (R.readout 0 .p t) = law (R.readout 0 .beta t) ∧
      residualA (R.readout 0 .beta t) = law (R.readout 0 .p t)

theorem family_bridge : (type_of% (@continuous_descriptor_family)) ↔
    familyArena.Law familyActual := Iff.rfl

theorem family_actual_law : familyArena.Law familyActual :=
  family_bridge.mp continuous_descriptor_family

abbrev recoveredMeasurableSignature : Signature where
  Params := ActivePhase
  State s := RegularDescriptor s
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def recoveredMeasurableActual : Realization recoveredMeasurableSignature :=
  realize _ (fun _ s D => recoveredParameter s D) (fun e => nomatch e)

def recoveredMeasurableArena : Arena where
  signature := recoveredMeasurableSignature
  Law R := ∀ s, Measurable (fun D => R.readout 0 s D)

theorem recoveredMeasurable_bridge : (type_of% (@recovered_measurable)) ↔
    recoveredMeasurableArena.Law recoveredMeasurableActual := Iff.rfl

theorem recoveredMeasurable_actual_law :
    recoveredMeasurableArena.Law recoveredMeasurableActual :=
  recoveredMeasurable_bridge.mp recovered_measurable

abbrev momentSignature : Signature where
  Params := ℕ
  State _ := CurveParameter
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def momentActual : Realization momentSignature :=
  realize _ (fun _ n t => curveG t*(t:ℝ)^n) (fun e => nomatch e)

def momentIntegralArena : Arena where
  signature := momentSignature
  Law R := ∀ n, averagedCompletion n = ∫ t, R.readout 0 n t ∂curveUniform

def momentIntegrableArena : Arena where
  signature := momentSignature
  Law R := ∀ n, Integrable (fun t => R.readout 0 n t) curveUniform

theorem momentIntegral_bridge : (type_of% (@averaged_parameter)) ↔
    momentIntegralArena.Law momentActual := Iff.rfl

theorem momentIntegrable_bridge : (type_of% (@moment_integrable)) ↔
    momentIntegrableArena.Law momentActual := Iff.rfl

theorem momentIntegral_actual_law : momentIntegralArena.Law momentActual :=
  momentIntegral_bridge.mp averaged_parameter

theorem momentIntegrable_actual_law : momentIntegrableArena.Law momentActual :=
  momentIntegrable_bridge.mp moment_integrable



abbrev recoveredSignature : Signature where
  Params := ActivePhase
  State _ := CurveParameter
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def recoveredArena : Arena where
  signature := recoveredSignature
  Law R := ∀ s t, R.readout 0 s t = (t:ℝ)

def recoveredActual : Realization recoveredSignature :=
  realize _ (fun _ s t => recoveredParameter s (curveDescriptor s t)) (fun e => nomatch e)

def recoveredRejected : Realization recoveredSignature :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ recoveredArena.Law recoveredRejected := by
  intro h
  have ht := h .p (⟨239/1000,by norm_num⟩ : CurveParameter)
  norm_num [recoveredRejected,realize] at ht

def recoveredRecord : Registration recoveredArena (type_of% (@recovered_curve)) where
  actual := recoveredActual
  bridge := Iff.rfl
  variation := ⟨recovered_curve,recoveredRejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨recoveredRejected,?_,rfl,rejected_law⟩
      intro j hj
      have he : j = i := by
        change Fin 1 at i j
        exact @Subsingleton.elim (Fin 1) inferInstance j i
      exact False.elim (hj he)
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(.p : ActivePhase),(⟨239/1000,by norm_num⟩ : CurveParameter),
      (⟨6/25,by norm_num⟩ : CurveParameter),?_⟩
    change recoveredParameter .p (curveDescriptor .p _) ≠ recoveredParameter .p (curveDescriptor .p _)
    rw [recovered_curve,recovered_curve]
    norm_num

def recoveredRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@recovered_curve)
    (type_of% (realize recoveredSignature (fun _ s t =>
      recoveredParameter s (curveDescriptor s t)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction.recovered,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction.recoveredRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨recoveredArena⟩, objectArena := .source ⟨recoveredArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source recoveredArena ⟨recoveredRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize recoveredSignature (fun _ s t =>
    recoveredParameter s (curveDescriptor s t)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction,
    definition := none, coordinates := #[0], readouts := #[{
      path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false,
      stateOperand := some #["arg","arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeInstalledFullLaw NativeObserverJointLaw NativeBorelCommonFlow
open NativeBorelFiniteCompleteObstruction NativeBorelFiniteCompleteObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u

abbrev recurrenceSignature : Signature where
  Params := Polynomial ℝ × ℕ
  State _ := ℕ
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def recurrenceActual : Realization recurrenceSignature :=
  realize _ (fun _ p n => ∑ i ∈ p.1.support, p.1.coeff i*averagedCompletion (p.2+n+i))
    (fun e => nomatch e)

def recurrenceArena : Arena where
  signature := recurrenceSignature
  Law R := ∀ (p : Polynomial ℝ), p ≠ 0 → ∀ N : ℕ, ∃ n : ℕ, R.readout 0 (p,N) n ≠ 0

theorem recurrence_bridge : (type_of% (@continuous_no_linear_recurrence)) ↔
    recurrenceArena.Law recurrenceActual := Iff.rfl

theorem recurrence_actual_law : recurrenceArena.Law recurrenceActual :=
  recurrence_bridge.mp continuous_no_linear_recurrence

def recurrenceRejected : Realization recurrenceSignature :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

private theorem recurrence_rejected_law : ¬ recurrenceArena.Law recurrenceRejected := by
  intro h
  obtain ⟨n,hn⟩ := h 1 one_ne_zero 0
  exact hn rfl

def recurrenceRecord : Registration recurrenceArena
    (type_of% (@continuous_no_linear_recurrence)) where
  actual := recurrenceActual
  bridge := recurrence_bridge
  variation := ⟨recurrence_actual_law,recurrenceRejected,recurrence_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨recurrenceRejected,?_,rfl,recurrence_rejected_law⟩
      intro j hj
      have he : j = i := @Subsingleton.elim (Fin 1) inferInstance j i
      exact False.elim (hj he)
    · intro i
      exact nomatch i
  dependence := by
    intro i
    have h := continuous_no_finite_linear_realization ℝ
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (averagedCompletion 0)
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 0
    have he : ∃ n : ℕ, averagedCompletion 0 ≠ averagedCompletion n := by
      by_contra! he
      apply h
      intro n
      simpa using (he n).symm
    obtain ⟨n, hn⟩ := he
    refine ⟨((1 : Polynomial ℝ),0),(0 : ℕ),n,?_⟩
    have hs : (1 : Polynomial ℝ).support = {0} := by
      simpa only [map_one] using (Polynomial.support_C (a := (1:ℝ)) one_ne_zero)
    change (∑ j ∈ (1 : Polynomial ℝ).support,
      (1 : Polynomial ℝ).coeff j*averagedCompletion (0+0+j)) ≠
      ∑ j ∈ (1 : Polynomial ℝ).support,
        (1 : Polynomial ℝ).coeff j*averagedCompletion (0+n+j)
    simp only [hs,Finset.sum_singleton,Polynomial.coeff_one_zero,one_mul,
      Nat.add_zero,Nat.zero_add]
    exact hn

structure LinearInput where
  Carrier : Type u
  additive : AddCommGroup Carrier
  scalar : @Module ℝ Carrier inferInstance additive.toAddCommMonoid
  finite : @Module.Finite ℝ Carrier inferInstance additive.toAddCommMonoid scalar
  operator : @Module.End ℝ Carrier inferInstance additive.toAddCommMonoid scalar
  vector : Carrier
  functional : @LinearMap ℝ ℝ inferInstance inferInstance (RingHom.id ℝ)
    Carrier ℝ additive.toAddCommMonoid inferInstance scalar inferInstance

def linearReadout (p : LinearInput.{u}) (n : ℕ) : ℝ :=
  letI := p.additive
  letI := p.scalar
  p.functional ((p.operator^n) p.vector)

abbrev linearSignature : Signature where
  Params := LinearInput.{u}
  State _ := ℕ
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def linearActual : Realization linearSignature.{u} :=
  realize _ (fun _ p n => linearReadout p n) (fun e => nomatch e)

def linearArena : Arena where
  signature := linearSignature.{u}
  Law R := ∀ p (N : ℕ), ¬ (∀ n, averagedCompletion (N+n) = R.readout 0 p n)

theorem linear_bridge : (type_of% (@continuous_no_finite_linear_realization.{u})) ↔
    linearArena.{u}.Law linearActual.{u} := by
  constructor
  · intro h p
    letI := p.additive
    letI := p.scalar
    letI := p.finite
    exact h p.Carrier p.operator p.vector p.functional
  · intro h V ha hm hf T x l N
    exact h ⟨V,ha,hm,hf,T,x,l⟩ N

theorem linear_actual_law : linearArena.{u}.Law linearActual.{u} :=
  linear_bridge.mp continuous_no_finite_linear_realization


structure FiniteInput where
  Carrier : Type u
  finite : Fintype Carrier
  measurable : MeasurableSpace Carrier
  singleton : @MeasurableSingletonClass Carrier measurable
  observer : @Observer Carrier finite
  emitter : @InstalledEmitter Carrier finite observer
  start : PMF Carrier

def inputReadout (p : FiniteInput.{u}) (n : ℕ) : ℝ :=
  letI := p.finite
  letI := p.measurable
  letI := p.singleton
  ∑ z : p.Carrier, (p.start z).toReal * (tailLaw p.observer p.emitter .p z).real {pAtom n 1}

abbrev installedSignature : Signature where
  Params := FiniteInput.{u}
  State _ := ℕ
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def installedActual : Realization installedSignature.{u} :=
  realize _ (fun _ p n => inputReadout p n) (fun e => nomatch e)

def installedArena : Arena where
  signature := installedSignature.{u}
  Law R := ∀ p (N : ℕ), ¬ (∀ n, averagedCompletion (N+n) = R.readout 0 p n)

theorem installed_bridge : (type_of% (@continuous_no_finite_complete.{u})) ↔
    installedArena.{u}.Law installedActual.{u} := by
  constructor
  · intro h p
    letI := p.finite
    letI := p.measurable
    letI := p.singleton
    exact h p.observer p.emitter p.start
  · intro h Z hf hm hs M e ρ N
    exact h ⟨Z,hf,hm,hs,M,e,ρ⟩ N

theorem installed_actual_law : installedArena.{u}.Law installedActual.{u} :=
  installed_bridge.mp continuous_no_finite_complete

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction
