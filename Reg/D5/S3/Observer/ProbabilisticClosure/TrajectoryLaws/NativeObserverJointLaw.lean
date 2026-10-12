import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeObserverJointLaw NativeFullResidual
open FourthSegmentStoppedLaw NativeConditionalControl.DepthLaw NativeConditionalControl.Tail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u

structure Complete where
  Z : Type u
  finite : Fintype Z
  measurable : MeasurableSpace Z
  singletons : @MeasurableSingletonClass Z measurable
  observer : @Observer Z finite
attribute [instance] Complete.finite Complete.measurable Complete.singletons

local instance : MeasurableSpace FiniteFields := ⊤
local instance : MeasurableSingletonClass FiniteFields := ⟨fun _ => trivial⟩

private def baseObserver : Observer FiniteFields where
  project := id
  init := PMF.pure initial.source.finiteFields
  update op f := PMF.pure ((finiteStep f op).getD f)
  init_refines := by intro z hz; simpa using (PMF.mem_support_pure_iff _ _).mp hz
  update_refines := by
    intro op z f hf z' hz'
    change finiteStep z op = some f at hf
    have he := (PMF.mem_support_pure_iff _ _).mp hz'
    change z' = (finiteStep z op).getD z at he
    simpa only [hf, Option.getD_some, id_eq] using he

def liftedBase : Complete.{u} :=
  ⟨ULift.{u} FiniteFields, inferInstance, ⊤, ⟨fun _ => trivial⟩, {
    project := ULift.down,
    init := (baseObserver.init).map ULift.up,
    update := fun op z => (baseObserver.update op z.down).map ULift.up,
    init_refines := by
      intro z hz
      obtain ⟨y, hy, hyz⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      subst z
      exact baseObserver.init_refines y hy,
    update_refines := by
      intro op z f hf z' hz'
      obtain ⟨y, hy, hyz⟩ := (PMF.mem_support_map_iff _ _ _).mp hz'
      subst z'
      exact baseObserver.update_refines op z.down f hf y hy }⟩

private theorem lifted_initial_mass :
    row liftedBase.observer [] (ULift.up initial.source.finiteFields) = 1 := by
  change ((PMF.pure initial.source.finiteFields).map ULift.up)
    (ULift.up initial.source.finiteFields) = 1
  rw [PMF.map, PMF.pure_bind]
  exact PMF.pure_apply_self _

abbrev jointSignature : Signature where
  Params := Complete.{u} × List Operation
  State _ := PMF Depth
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Measure ((Depth × Stream) × p.1.Z)
  Anchor := Empty
  finiteAnchor := inferInstance

def jointActual : Realization jointSignature :=
  realize jointSignature (fun _ p μ => actualLaw p.1.observer μ p.2.length)
    (fun e => nomatch e)
def jointRejected : Realization jointSignature :=
  realize jointSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem initial_event : nativeEvent [] initial = Set.univ := by
  rw [event_eq [] initial rfl]
  ext t
  simp [prefixCylinder, Prefix, readPrefix, readLetters]

private theorem joint_dependence_universe : ObservationalDependence jointSignature.{u} jointActual := by
  intro i
  cases i
  let C : Complete.{u} := liftedBase
  letI : MeasurableSpace C.Z := C.measurable
  letI : MeasurableSingletonClass C.Z := C.singletons
  let z : C.Z := ULift.up initial.source.finiteFields
  let A : Set ((Depth × Stream) × C.Z) :=
    (nativeEvent [] initial ∩ {t : Depth × Stream |
      t.1 = 1 ∧ rawTail t.2 (readLetters []).length ∈ Set.univ}) ×ˢ {z}
  refine ⟨(C, []), PMF.pure 1, PMF.pure 2, ?_⟩
  intro he
  have hm := congrArg (fun L : Measure ((Depth × Stream) × C.Z) => L A) he
  have h1 := @ordered_history_factorization C.Z C.finite C.measurable C.singletons
    C.observer (PMF.pure 1) [] initial rfl 1 z Set.univ MeasurableSet.univ
  have h2 := @ordered_history_factorization C.Z C.finite C.measurable C.singletons
    C.observer (PMF.pure 2) [] initial rfl 1 z Set.univ MeasurableSet.univ
  change actualLaw C.observer (PMF.pure 1) [].length A =
    actualLaw C.observer (PMF.pure 2) [].length A at hm
  dsimp only [A] at hm
  rw [h1, h2] at hm
  have hz : row C.observer [] z = 1 := lifted_initial_mass
  simp only [hz, PMF.pure_apply, likelihood, readLetters, wordMass, List.map_nil,
    List.prod_nil, measure_univ] at hm
  simp at hm

def factorArena : Arena where
  signature := jointSignature
  Law R := ∀ (C : Complete.{u}) (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState), run h = some c → ∀ (k : Depth) (z : C.Z)
    (E : Set Stream), MeasurableSet E →
    R.readout () (C, h) μ
      ((nativeEvent h c ∩ {t : Depth × Stream |
        t.1 = k ∧ rawTail t.2 (readLetters h).length ∈ E}) ×ˢ {z}) =
      μ k * likelihood h k * row C.observer h z * rawReadLaw (rate k) E

private theorem factorRejected_law : ¬ factorArena.{u}.Law jointRejected := by
  intro law
  let C : Complete.{u} := liftedBase
  letI : MeasurableSpace C.Z := C.measurable
  letI : MeasurableSingletonClass C.Z := C.singletons
  have h := law C (PMF.pure 1) [] initial rfl 1 (ULift.up initial.source.finiteFields)
    Set.univ MeasurableSet.univ
  have hz : row C.observer [] (ULift.up initial.source.finiteFields) = 1 := lifted_initial_mass
  change (0 : Measure ((Depth × Stream) × C.Z)) _ = _ at h
  simp only [Measure.coe_zero, Pi.zero_apply, hz, PMF.pure_apply_self, likelihood,
    readLetters, wordMass, List.map_nil, List.prod_nil, measure_univ, mul_one] at h
  exact zero_ne_one h

def factorRecord : Registration factorArena.{u}
    (type_of% (@ordered_history_factorization.{u})) where
  actual := jointActual
  bridge := by
    constructor
    · intro T C μ h c hc k z E hE
      exact T C.observer μ h c hc k z E hE
    · intro T Z f m singleton M μ h c hc k z E hE
      exact T ⟨Z, f, m, singleton, M⟩ μ h c hc k z E hE
  variation := ⟨(fun C μ h c hc k z E hE =>
    ordered_history_factorization C.observer μ h c hc k z E hE),
    jointRejected, factorRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨jointRejected, ?_, rfl, factorRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := joint_dependence_universe

def conditionalArena : Arena where
  signature := jointSignature
  Law R := ∀ (C : Complete.{u}) (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c),
    ProbabilityTheory.cond (R.readout () (C, h) μ) (nativeEvent h c ×ˢ Set.univ) =
      (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).prod (row C.observer h).toMeasure

private theorem conditionalRejected_law : ¬ conditionalArena.{u}.Law jointRejected := by
  intro law
  let C : Complete.{u} := liftedBase
  have h := congrArg (fun L : Measure ((Depth × Stream) × C.Z) => L Set.univ)
    (law C (PMF.pure 1) [] initial rfl)
  simp [jointRejected, realize, initial_event, ProbabilityTheory.cond] at h

def conditionalRecord : Registration conditionalArena.{u}
    (type_of% (@conditional_history_product.{u})) where
  actual := jointActual
  bridge := by
    constructor
    · intro T C μ h c hc
      exact T C.observer μ h c hc
    · intro T Z f m singleton M μ h c hc
      exact T ⟨Z, f, m, singleton, M⟩ μ h c hc
  variation := ⟨(fun C μ h c hc => conditional_history_product C.observer μ h c hc),
    jointRejected, conditionalRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨jointRejected, ?_, rfl, conditionalRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := joint_dependence_universe

def factorRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ordered_history_factorization.{u})
    (type_of% (realize jointSignature.{u}
      (fun _ p μ => actualLaw p.1.observer μ p.2.length) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.factor,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.factorRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨factorArena⟩, objectArena := .source ⟨factorArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source factorArena ⟨factorRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize jointSignature.{u}
    (fun _ p μ => actualLaw p.1.observer μ p.2.length) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw,
    definition := none, coordinates := #[0, 4, 6], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def conditionalRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@conditional_history_product.{u})
    (type_of% (realize jointSignature.{u}
      (fun _ p μ => actualLaw p.1.observer μ p.2.length) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.conditional,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.conditionalRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨conditionalArena⟩, objectArena := .source ⟨conditionalArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source conditionalArena ⟨conditionalRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize jointSignature.{u}
    (fun _ p μ => actualLaw p.1.observer μ p.2.length) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw,
    definition := none, coordinates := #[0, 4, 6], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def sameKArena : Arena where
  signature := jointSignature
  Law R := ∀ (C : Complete.{u}) (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c),
    (ProbabilityTheory.cond (R.readout () (C, h) μ) (nativeEvent h c ×ˢ Set.univ)).map
      (Prod.map (fun t : Depth × Stream =>
        (t.1, rawTail t.2 (readLetters h).length)) id) =
      (jointLaw (posterior μ h c hc)).prod (row C.observer h).toMeasure

private theorem sameKRejected_law : ¬ sameKArena.{u}.Law jointRejected := by
  intro law
  let C : Complete.{u} := liftedBase
  have h := congrArg (fun L : Measure ((Depth × Stream) × C.Z) => L Set.univ)
    (law C (PMF.pure 1) [] initial rfl)
  simp [jointRejected, realize, ProbabilityTheory.cond] at h

def sameKRecord : Registration sameKArena.{u} (type_of% (@sameK_private_tail.{u})) where
  actual := jointActual
  bridge := by
    constructor
    · intro T C μ h c hc
      exact T C.observer μ h c hc
    · intro T Z f m singleton M μ h c hc
      exact T ⟨Z, f, m, singleton, M⟩ μ h c hc
  variation := ⟨(fun C μ h c hc => sameK_private_tail C.observer μ h c hc),
    jointRejected, sameKRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨jointRejected, ?_, rfl, sameKRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := joint_dependence_universe

abbrev rowSignature : Signature where
  Params := Complete.{u}
  State _ := List Operation
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := PMF C.Z
  Anchor := Empty
  finiteAnchor := inferInstance

def rowActual : Realization rowSignature :=
  realize rowSignature (fun _ C h => row C.observer h) (fun e => nomatch e)
def rowRejected : Realization rowSignature :=
  realize rowSignature (fun _ C _ => C.observer.init) (fun e => nomatch e)

def rowArena : Arena where
  signature := rowSignature
  Law R := ∀ (C : Complete.{u}) (h : List Operation) (c : AcquiredNativeState),
    run h = some c →
    (∀ z ∈ (R.readout () C h).support, C.observer.project z = c.source.finiteFields) ∧
    (∀ op : Operation, R.readout () C (h ++ [op]) =
      (R.readout () C h).bind (C.observer.update op)) ∧
    ∃ nf : PrefixForm, render nf = h ∧ c = reconstruct nf ∧ PrefixFacts nf c

private def afterAlpha : AcquiredNativeState :=
  ⟨⟨⟨.seed (some 0), emptyRegisters⟩, 0⟩, ⟨1, 0⟩⟩

private theorem rowRejected_law : ¬ rowArena.{u}.Law rowRejected := by
  intro law
  let C : Complete.{u} := liftedBase
  let z : C.Z := ULift.up initial.source.finiteFields
  have hz : z ∈ C.observer.init.support := by
    change row C.observer [] z ≠ 0
    rw [show row C.observer [] z = 1 from lifted_initial_mass]
    exact one_ne_zero
  have h := (law C [.read 0] afterAlpha rfl).1 z hz
  have hc := congrArg FiniteFields.control h
  simp [C, z, liftedBase, initial, afterAlpha] at hc

def rowRecord : Registration rowArena.{u} (type_of% (@actual_row_refines.{u})) where
  actual := rowActual
  bridge := by
    constructor
    · intro T C h c hc
      exact T C.observer h c hc
    · intro T Z f m singleton M h c hc
      exact T ⟨Z, f, m, singleton, M⟩ h c hc
  variation := ⟨(fun C h c hc => actual_row_refines C.observer h c hc),
    rowRejected, rowRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rowRejected, ?_, rfl, rowRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let C : Complete.{u} := liftedBase
    let z : C.Z := ULift.up initial.source.finiteFields
    refine ⟨C, [], [.read 0], ?_⟩
    intro he
    have hz : z ∈ (row C.observer []).support := by
      change row C.observer [] z ≠ 0
      rw [show row C.observer [] z = 1 from lifted_initial_mass]
      exact one_ne_zero
    change row C.observer [] = row C.observer [.read 0] at he
    rw [he] at hz
    have hp := (actual_row_refines C.observer [.read 0] afterAlpha rfl).1 z hz
    have hc := congrArg FiniteFields.control hp
    simp [C, z, liftedBase, initial, afterAlpha] at hc

open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open scoped BigOperators

abbrev riskSignature : Signature where
  Params := Complete.{u} × PMF Depth × ActivePhase
  State p := PhaseHistory p.2.2 → p.1.Z → Measure (ValidTail p.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def riskActual : Realization riskSignature :=
  realize riskSignature (fun _ p D => fullRisk p.1.observer p.2.1 p.2.2 D)
    (fun e => nomatch e)
def riskRejected : Realization riskSignature :=
  realize riskSignature (fun _ p D => fullRisk p.1.observer p.2.1 p.2.2 D + 1)
    (fun e => nomatch e)

def riskArena : Arena where
  signature := riskSignature
  Law R := ∀ (C : Complete.{u}) (μ : PMF Depth) (s : ActivePhase)
    (D : PhaseHistory s → C.Z → Measure (ValidTail s)),
    (∀ H : PhaseHistory s,
      IsProbabilityMeasure (rawTarget μ H.val.1 H.val.2 s) ∧
      IsProbabilityMeasure (fullTarget C.observer μ H.val.1 H.val.2) ∧
      fullTarget C.observer μ H.val.1 H.val.2 =
        (rawTarget μ H.val.1 H.val.2 s).map (fullRenderer H.val.2 s) ∧
      (rawTarget μ H.val.1 H.val.2 s).map Subtype.val =
        FourthSegmentLawRecovery.WordLaw.wordMixture
          (posterior μ H.val.1 H.val.2 H.property.1) s ∧
      (ProbabilityTheory.cond (actualLaw C.observer μ H.val.1.length)
        (nativeEvent H.val.1 H.val.2 ×ˢ Set.univ)).map Prod.snd = (row C.observer H.val.1).toMeasure ∧
      (∀ z ∈ (row C.observer H.val.1).support, C.observer.project z = H.val.2.source.finiteFields) ∧
      (∀ op : Operation, row C.observer (H.val.1 ++ [op]) = (row C.observer H.val.1).bind (C.observer.update op)) ∧
      (∃ nf : PrefixForm, render nf = H.val.1 ∧ H.val.2 = reconstruct nf ∧
        PrefixFacts nf H.val.2) ∧
      (∀ (ω : Stream) (d : AcquiredNativeState) (op : Operation),
        nextNative H.val.2 ω = some (op, d) →
        deleteBlock (fullTranscript H.val.2 ω) =
          fullTranscript d (rawTail ω (readCost op))) ∧
      (∀ (k : Depth) (z : C.Z) (E : Set Stream), MeasurableSet E →
        actualLaw C.observer μ H.val.1.length
          ((nativeEvent H.val.1 H.val.2 ∩ {t : Depth × Stream |
            t.1 = k ∧ rawTail t.2 (readLetters H.val.1).length ∈ E}) ×ˢ {z}) =
          μ k * likelihood H.val.1 k * row C.observer H.val.1 z * rawReadLaw (rate k) E) ∧
      (∀ ω : Stream, ω ∈ prefixCylinder (readLetters H.val.1) →
        fullTranscript initial ω H.val.1.length =
          some (H.val.1, H.val.2.source.finiteFields,
            eventBlocks initial.source.finiteFields H.val.1) ∧
        (eventBlocks initial.source.finiteFields H.val.1).foldl replayBlock
          initial.source.finiteFields = H.val.2.source.finiteFields ∧
        originalView ((eventBlocks initial.source.finiteFields H.val.1).foldl replayBlock
          initial.source.finiteFields) = originalView H.val.2.source.finiteFields)) ∧
    R.readout () (C, μ, s) D = rawRisk C.observer μ s D

private theorem targetRisk_zero (C : Complete.{u}) (μ : PMF Depth) (s : ActivePhase) :
    rawRisk C.observer μ s (fun H _ => rawTarget μ H.val.1 H.val.2 s) = 0 := by
  simp [rawRisk, measurableTotalVariation]

private theorem riskRejected_law : ¬ riskArena.{u}.Law riskRejected := by
  intro law
  let C : Complete.{u} := liftedBase
  let μ : PMF Depth := PMF.pure 1
  let D : PhaseHistory .p → C.Z → Measure (ValidTail .p) :=
    fun H _ => rawTarget μ H.val.1 H.val.2 .p
  have h := (law C μ .p D).2
  change fullRisk C.observer μ .p D + 1 = rawRisk C.observer μ .p D at h
  rw [(native_history_risk_transport C.observer μ .p D).2,
    targetRisk_zero C μ .p] at h
  simp at h

private def activeForm : PrefixForm :=
  ⟨[], .acquired 1 (.segment 0 1 (.segment 0 0 (.segment 0 0 (.active 0 .p))))⟩
private def activeHistory : PhaseHistory .p :=
  ⟨(render activeForm, reconstruct activeForm), run_render activeForm, rfl⟩

private theorem zeroRisk_positive (C : Complete.{u}) (μ : PMF Depth) :
    1 ≤ rawRisk C.observer μ .p (fun _ _ => 0) := by
  let H : PhaseHistory .p := activeHistory
  haveI : IsProbabilityMeasure (rawTarget μ H.val.1 H.val.2 .p) :=
    ((native_history_risk_transport C.observer μ .p (fun _ _ => 0)).1 H).1
  have ht : 1 ≤ measurableTotalVariation 0 (rawTarget μ H.val.1 H.val.2 .p) := by
    unfold measurableTotalVariation
    apply le_iSup_of_le ⟨Set.univ, MeasurableSet.univ⟩
    simp
  unfold rawRisk
  apply le_iSup_of_le H
  calc
    1 = ∑ z, row C.observer H.val.1 z * 1 := by
      have hp := (row C.observer H.val.1).tsum_coe
      rw [tsum_fintype] at hp
      simpa only [mul_one] using hp.symm
    _ ≤ _ := Finset.sum_le_sum (by intro z _; gcongr)

def riskRecord : Registration riskArena.{u} (type_of% (@native_history_risk_transport.{u})) where
  actual := riskActual
  bridge := by
    constructor
    · intro T C μ s D
      exact T C.observer μ s D
    · intro T Z f m singleton M μ s D
      exact T ⟨Z, f, m, singleton, M⟩ μ s D
  variation := ⟨(fun C μ s D => native_history_risk_transport C.observer μ s D),
    riskRejected, riskRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨riskRejected, ?_, rfl, riskRejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let C : Complete.{u} := liftedBase
    let μ : PMF Depth := PMF.pure 1
    let D : PhaseHistory .p → C.Z → Measure (ValidTail .p) :=
      fun H _ => rawTarget μ H.val.1 H.val.2 .p
    refine ⟨(C, μ, .p), D, (fun _ _ => 0), ?_⟩
    change fullRisk C.observer μ .p D ≠ fullRisk C.observer μ .p (fun _ _ => 0)
    rw [(native_history_risk_transport C.observer μ .p D).2,
      (native_history_risk_transport C.observer μ .p (fun _ _ => 0)).2,
      targetRisk_zero C μ .p]
    intro h
    have hp := zeroRisk_positive C μ
    rw [← h] at hp
    simp at hp

def sameKRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sameK_private_tail.{u})
    (type_of% (realize jointSignature.{u} (fun _ p μ => actualLaw p.1.observer μ p.2.length) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.sameK,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.sameKRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨sameKArena⟩, objectArena := .source ⟨sameKArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source sameKArena ⟨sameKRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize jointSignature.{u} (fun _ p μ => actualLaw p.1.observer μ p.2.length) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw,
    definition := none, coordinates := #[0, 4, 6], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def rowRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_row_refines.{u})
    (type_of% (realize rowSignature.{u} (fun _ C h => row C.observer h) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.row,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.rowRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨rowArena⟩, objectArena := .source ⟨rowArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source rowArena ⟨rowRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize rowSignature.{u} (fun _ C h => row C.observer h) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw,
    definition := none, coordinates := #[0, 4], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def riskRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_history_risk_transport.{u})
    (type_of% (realize riskSignature.{u} (fun _ p D => fullRisk p.1.observer p.2.1 p.2.2 D) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.risk,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw.riskRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨riskArena⟩, objectArena := .source ⟨riskArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source riskArena ⟨riskRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize riskSignature.{u} (fun _ p D => fullRisk p.1.observer p.2.1 p.2.2 D) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw,
    definition := none, coordinates := #[0, 4, 5, 6], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms factorRegistration
#print axioms conditionalRegistration
#print axioms sameKRegistration
#print axioms rowRegistration
#print axioms riskRegistration

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
