import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory Set
universe u

structure PredicateFamily where
  A : Type u
  accept : Set A

abbrev hitSignature : Signature where
  Params := PredicateFamily.{u}
  State C := ℕ → C.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def hitActual : Realization hitSignature :=
  realize hitSignature (fun _ C ω => firstHit C.accept ω) (fun e => nomatch e)
def hitRejected : Realization hitSignature :=
  realize hitSignature (fun _ _ _ => none) (fun e => nomatch e)
def hitArena : Arena where
  signature := hitSignature.{u}
  Law R := ∀ {A : Type u} [MeasurableSpace A] (accept : Set A) (ω : ℕ → A) (n : ℕ),
    R.readout () ⟨A,accept⟩ ω = some n ↔ ω n ∈ accept ∧ ∀ i < n, ω i ∉ accept

private theorem hit_rejected : ¬ hitArena.{u}.Law hitRejected := by
  intro h
  have hn := (h (Set.univ : Set (ULift.{u} Bool)) (fun _ => ⟨false⟩) 0).mpr
    ⟨Set.mem_univ _,fun i hi => by omega⟩
  cases hn

def hitRecord : Registration hitArena.{u} (type_of% (@first_hit_some.{u})) where
  actual := hitActual
  bridge := Iff.rfl
  variation := ⟨first_hit_some,hitRejected,hit_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨hitRejected,?_,rfl,hit_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let a : ULift.{u} Bool := ⟨false⟩
    let b : ULift.{u} Bool := ⟨true⟩
    refine ⟨⟨ULift.{u} Bool,{a}⟩,(fun _ => a),(fun _ => b),?_⟩
    intro he
    change firstHit {a} (fun _ => a) = firstHit {a} (fun _ => b) at he
    have ha : firstHit {a} (fun _ => a) = some 0 :=
      (first_hit_some _ _ 0).mpr ⟨rfl,fun i hi => by omega⟩
    have hb : firstHit {a} (fun _ => b) = none := by
      simp [firstHit,show b ≠ a by decide]
    rw [ha,hb] at he
    cases he

def hitRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@first_hit_some.{u}) (type_of% (realize hitSignature.{u}
      (fun _ C ω => firstHit C.accept ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `FreshServiceRestart.first_hit_some.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart.hitRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨hitArena⟩, objectArena := .source ⟨hitArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source hitArena ⟨hitRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize hitSignature.{u} (fun _ C ω => firstHit C.accept ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart,
    definition := none, coordinates := #[0,2],
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 3, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

structure ServiceFamily where
  A : Type u
  accept : Set A
  fallback : A

abbrev restartSignature : Signature where
  Params := ServiceFamily.{u}
  State C := ℕ → C.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := C.A × (ℕ → C.A)
  Anchor := Empty
  finiteAnchor := inferInstance

def restartActual : Realization restartSignature :=
  realize restartSignature (fun _ C ω => restart C.accept C.fallback ω) (fun e => nomatch e)
def restartRejected : Realization restartSignature :=
  realize restartSignature (fun _ C _ => (C.fallback,fun _ => C.fallback)) (fun e => nomatch e)
def restartArena : Arena where
  signature := restartSignature.{u}
  Law R := ∀ {A : Type u} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (accept : Set A) (fallback : A), MeasurableSet accept → μ accept ≠ 0 →
    (Measure.infinitePi (fun _ : ℕ => μ)).map (R.readout () ⟨A,accept,fallback⟩) =
      (ProbabilityTheory.cond μ accept).prod (Measure.infinitePi (fun _ : ℕ => μ))

private theorem restart_rejected : ¬ restartArena.{u}.Law restartRejected := by
  intro h
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  have he := h (Measure.dirac a) univ b MeasurableSet.univ (by simp)
  have hs := congrArg (fun ν => ν (({a} : Set (ULift.{u} Bool)) ×ˢ univ)) he
  simp [restartRejected,realize,Measure.map_const,Measure.prod_prod,
    ProbabilityTheory.cond_univ,show b ≠ a by decide] at hs

def restartRecord : Registration restartArena.{u} (type_of% (@first_acceptance_restart.{u})) where
  actual := restartActual
  bridge := Iff.rfl
  variation := ⟨first_acceptance_restart,restartRejected,restart_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨restartRejected,?_,rfl,restart_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let a : ULift.{u} Bool := ⟨false⟩
    let b : ULift.{u} Bool := ⟨true⟩
    refine ⟨⟨ULift.{u} Bool,univ,a⟩,(fun _ => a),(fun _ => b),?_⟩
    intro he
    have ha := (first_hit_some univ (fun _ => a) 0).mpr ⟨mem_univ _,fun i hi => by omega⟩
    have hb := (first_hit_some univ (fun _ => b) 0).mpr ⟨mem_univ _,fun i hi => by omega⟩
    have h0 := congrArg Prod.fst he
    simp only [restartActual,realize,restart,ha,hb] at h0
    norm_num [a,b] at h0

def restartRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@first_acceptance_restart.{u}) (type_of% (realize restartSignature.{u}
      (fun _ C ω => restart C.accept C.fallback ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `FreshServiceRestart.first_acceptance_restart.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart.restartRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨restartArena⟩, objectArena := .source ⟨restartArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source restartArena ⟨restartRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize restartSignature.{u} (fun _ C ω => restart C.accept C.fallback ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart,
    definition := none, coordinates := #[0,4,5],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

abbrev repeatedSignature : Signature where
  Params := ServiceFamily.{u}
  State C := ℕ → C.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := ℕ → C.A
  Anchor := Empty
  finiteAnchor := inferInstance
def repeatedActual : Realization repeatedSignature :=
  realize repeatedSignature (fun _ C ω => draws C.accept C.fallback ω) (fun e => nomatch e)
def repeatedRejected : Realization repeatedSignature :=
  realize repeatedSignature (fun _ C _ _ => C.fallback) (fun e => nomatch e)
def repeatedArena : Arena where
  signature := repeatedSignature.{u}
  Law R := ∀ {A : Type u} [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure A) [IsProbabilityMeasure μ] (accept : Set A) (fallback : A)
    (ha : MeasurableSet accept) (hpos : μ accept ≠ 0),
    Measurable (R.readout () ⟨A,accept,fallback⟩) ∧
    (Measure.infinitePi (fun _ : ℕ => μ)).map (R.readout () ⟨A,accept,fallback⟩) =
      Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond μ accept) ∧
    (∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ), ∀ n,
      firstHit accept (unused accept fallback n ω) ≠ none)

private theorem repeated_rejected : ¬ repeatedArena.{u}.Law repeatedRejected := by
  intro h
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  have he := (h (Measure.dirac a) univ b MeasurableSet.univ (by simp)).2.1
  have hs := congrArg (fun ν => ν {ω | ω 0 = a}) he
  have hm : MeasurableSet {ω : ℕ → ULift.{u} Bool | ω 0 = a} :=
    (measurableSet_singleton a).preimage (measurable_pi_apply 0)
  have hr : (Measure.infinitePi (fun _ : ℕ => Measure.dirac a)) {ω | ω 0 = a} = 1 := by
    have hh := congrArg (fun ν => ν {a})
      (Measure.infinitePi_map_eval (fun _ : ℕ => Measure.dirac a) 0)
    rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton a)] at hh
    simpa using hh
  simp [repeatedRejected,realize,show b ≠ a by decide,ProbabilityTheory.cond_univ,
    Measure.map_const,hr] at hs

def repeatedRecord : Registration repeatedArena.{u} (type_of% (@repeated_acceptance_law.{u})) where
  actual := repeatedActual
  bridge := Iff.rfl
  variation := ⟨repeated_acceptance_law,repeatedRejected,repeated_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨repeatedRejected,?_,rfl,repeated_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let a : ULift.{u} Bool := ⟨false⟩
    let b : ULift.{u} Bool := ⟨true⟩
    refine ⟨⟨ULift.{u} Bool,univ,a⟩,(fun _ => a),(fun _ => b),?_⟩
    intro he
    have ha := (first_hit_some univ (fun _ => a) 0).mpr ⟨mem_univ _,fun i hi => by omega⟩
    have hb := (first_hit_some univ (fun _ => b) 0).mpr ⟨mem_univ _,fun i hi => by omega⟩
    have h0 := congrFun he 0
    simp only [repeatedActual,realize,draws,unused,restart,ha,hb] at h0
    norm_num [a,b] at h0

def repeatedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_acceptance_law.{u}) (type_of% (realize repeatedSignature.{u}
      (fun _ C ω => draws C.accept C.fallback ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `FreshServiceRestart.repeated_acceptance_law.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart.repeatedRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨repeatedArena⟩, objectArena := .source ⟨repeatedArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source repeatedArena ⟨repeatedRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize repeatedSignature.{u} (fun _ C ω => draws C.accept C.fallback ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart,
    definition := none, coordinates := #[0,6,7],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg","arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FreshServiceRestart
