/- GID: D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeMonotonicity/HorizontalSaturationSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Budget expansion can repair one family; saturation needs a new coordinate. -/
/- Library-search audit trail (2026-08-25):
   * The FPOD source was checked at Section 89, including Principle and Definition 89.1.
   * `SubfamilyInadequacyPersistence` exactly proves the arbitrary-subfamily negative half.
   * `FactorizedTranscriptKernelBarrier` exactly proves the repeated-kernel negative half.
   * D5 searches found canonical `Concept`, `jointReadout`, `Refines`, and `TargetAdequate`.
   * Pinned Mathlib hits were `Function.FactorsThrough`, `Function.Injective`, `Setoid.ker`,
     `Set.iSup`, and probability kernels; none supplies the budget/language separation.
   * Primality has no role in any declaration in this module. -/

import D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.SubfamilyInadequacyPersistence
import D5.S3.Observer.MeasureSeparation.FactorizedTranscriptKernelBarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.HorizontalSaturationSeparation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion
open D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.SubfamilyInadequacyPersistence
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Observer.MeasureSeparation.FactorizedTranscriptKernelBarrier

/-- A typed sensor family indexed by `I`, with a possibly dependent value type. -/
abbrev InterfaceFamily (I X : Type*) (V : I → Type*) :=
  ∀ i, Concept X (V i)

/-- The union of every sensor in a typed family is its canonical dependent joint readout. -/
def interfaceUnion {I X : Type*} {V : I → Type*}
    (family : InterfaceFamily I X V) : Concept X (∀ i, V i) :=
  jointReadout family

/-- The union restricted to a selected subset of the available sensor indices. -/
def subfamilyUnion {I X : Type*} {V : I → Type*}
    (family : InterfaceFamily I X V) (selected : Set I) :
    Concept X (∀ i : selected, V i.1) :=
  jointReadout (fun i : selected => family i.1)

/-- A selected budget is insufficient when it fails now but a strict expansion using only
already available sensors succeeds. -/
def BudgetInsufficient {I X Target : Type*} {V : I → Type*}
    (family : InterfaceFamily I X V) (target : Concept X Target)
    (selected : Set I) : Prop :=
  ¬TargetAdequate (subfamilyUnion family selected) target ∧
    ∃ expanded : Set I, selected ⊂ expanded ∧
      TargetAdequate (subfamilyUnion family expanded) target

/-- The observation language is insufficient when even the union of all allowed sensors
cannot recover the target. -/
def ObservationLanguageInsufficient {I X Target : Type*} {V : I → Type*}
    (family : InterfaceFamily I X V) (target : Concept X Target) : Prop :=
  ¬TargetAdequate (interfaceUnion family) target

/-- Semantic completion preserves the full old profile and adds the target as a new coordinate. -/
def semanticCompletion {I X Target : Type*} {V : I → Type*}
    (family : InterfaceFamily I X V) (target : Concept X Target) :
    Concept X ((∀ i, V i) × Target) :=
  conceptJoin (interfaceUnion family) target

/-- Semantic completion retains every old sensor and makes the target recoverable. -/
theorem semantic_completion_preserves_family_and_recovers_target
    {I X Target : Type*} {V : I → Type*}
    (family : InterfaceFamily I X V) (target : Concept X Target) :
    Refines (interfaceUnion family) (semanticCompletion family target) ∧
      TargetAdequate (semanticCompletion family target) target := by
  have universal := concept_join_universal (interfaceUnion family) target
    (semanticCompletion family target)
  simpa only [semanticCompletion, TargetAdequate] using
    And.intro universal.1 universal.2.1
#print axioms semantic_completion_preserves_family_and_recovers_target

/-- Semantic completion is the least common refinement retaining the old family and target. -/
theorem semantic_completion_minimal
    {I X Target Candidate : Type*} {V : I → Type*}
    (family : InterfaceFamily I X V) (target : Concept X Target)
    (candidate : Concept X Candidate)
    (familyVisible : Refines (interfaceUnion family) candidate)
    (targetVisible : TargetAdequate candidate target) :
    Refines (semanticCompletion family target) candidate := by
  exact (concept_join_universal (interfaceUnion family) target candidate).2.2
    familyVisible targetVisible
#print axioms semantic_completion_minimal

/-- The budget witness has one constant sensor and one identity sensor of the same output type. -/
def budgetSensorFamily : InterfaceFamily Bool Bool (fun _ => Bool) :=
  fun sensor state => if sensor then state else false

/-- The language witness consists of a single constant sensor. -/
def constantSensorFamily : InterfaceFamily Unit Bool (fun _ => Unit) :=
  fun _ => booleanInterface

private theorem budget_sensor_full_adequate :
    TargetAdequate (interfaceUnion budgetSensorFamily) booleanTarget := by
  refine ⟨fun readings => readings true, ?_⟩
  funext state
  simp [booleanTarget, interfaceUnion, budgetSensorFamily, jointReadout]

/-- The family-visibility hypothesis in semantic minimality is necessary: a constant
candidate sees the constant target but cannot recover the completed budget witness. -/
theorem family_visibility_is_necessary :
    TargetAdequate (fun _ : Bool => ()) (fun _ : Bool => ()) ∧
      ¬Refines
        (semanticCompletion budgetSensorFamily (fun _ : Bool => ()))
        (fun _ : Bool => ()) := by
  constructor
  · exact ⟨id, rfl⟩
  · rintro ⟨factor, factors⟩
    have equalOutputs :
        semanticCompletion budgetSensorFamily (fun _ : Bool => ()) false =
          semanticCompletion budgetSensorFamily (fun _ : Bool => ()) true := by
      calc
        _ = factor () := by
          simpa only [Function.comp_apply] using congrFun factors false
        _ = _ := by
          simpa only [Function.comp_apply] using (congrFun factors true).symm
    have coordinateEquality :=
      congrArg (fun output => output.1 true) equalOutputs
    change false = true at coordinateEquality
    exact Bool.false_ne_true coordinateEquality
#print axioms family_visibility_is_necessary

/-- The target-visibility hypothesis in semantic minimality is necessary: the old constant
family sees itself but cannot recover a completion carrying the Boolean target. -/
theorem target_visibility_is_necessary :
    Refines (interfaceUnion constantSensorFamily)
        (interfaceUnion constantSensorFamily) ∧
      ¬Refines (semanticCompletion constantSensorFamily booleanTarget)
        (interfaceUnion constantSensorFamily) := by
  constructor
  · exact ⟨id, rfl⟩
  · rintro ⟨factor, factors⟩
    have sameReadout :
        interfaceUnion constantSensorFamily false =
          interfaceUnion constantSensorFamily true := rfl
    have equalOutputs :
        semanticCompletion constantSensorFamily booleanTarget false =
          semanticCompletion constantSensorFamily booleanTarget true := by
      calc
        _ = factor (interfaceUnion constantSensorFamily false) := by
          simpa only [Function.comp_apply] using congrFun factors false
        _ = factor (interfaceUnion constantSensorFamily true) :=
          congrArg factor sameReadout
        _ = _ := by
          simpa only [Function.comp_apply] using (congrFun factors true).symm
    have targetEquality := congrArg Prod.snd equalOutputs
    exact Bool.false_ne_true (by
      simpa only [semanticCompletion, conceptJoin, booleanTarget, id_eq] using
        targetEquality)
#print axioms target_visibility_is_necessary

/-- Named budget-insufficiency witness: the constant sensor fails, while adding the already
available identity sensor repairs exact target recovery. -/
theorem budget_insufficiency_witness :
    BudgetInsufficient budgetSensorFamily booleanTarget ({false} : Set Bool) := by
  constructor
  · intro selectedAdequate
    have fiberConstant :=
      (target_adequate_iff_fiber_constant
        (subfamilyUnion budgetSensorFamily ({false} : Set Bool))
        booleanTarget).mp selectedAdequate
    have sameSelected :
        subfamilyUnion budgetSensorFamily ({false} : Set Bool) false =
          subfamilyUnion budgetSensorFamily ({false} : Set Bool) true := by
      funext member
      rcases member with ⟨sensor, sensorSelected⟩
      have sensorFalse : sensor = false := by
        simpa only [Set.mem_singleton_iff] using sensorSelected
      subst sensor
      rfl
    apply Bool.false_ne_true
    simpa only [booleanTarget, id_eq] using
      (fiberConstant (x := false) (y := true) sameSelected)
  · refine ⟨Set.univ, Set.ssubset_iff_exists.mpr ?_, ?_⟩
    · exact ⟨Set.subset_univ _, true, Set.mem_univ true, by simp⟩
    · refine ⟨fun readings => readings ⟨true, Set.mem_univ true⟩, ?_⟩
      funext state
      simp [booleanTarget, subfamilyUnion, budgetSensorFamily, jointReadout]
#print axioms budget_insufficiency_witness

/-- Named language-insufficiency witness: every subfamily is inadequate, and the union remains
the factor for every iid repetition, so repeated sampling never identifies the Boolean target. -/
theorem observation_language_insufficiency_witness :
    ObservationLanguageInsufficient constantSensorFamily booleanTarget ∧
      (∀ selected : Set Unit,
        ¬TargetAdequate (subfamilyUnion constantSensorFamily selected) booleanTarget) ∧
      ∀ n : Nat,
        KernelFactorsThrough (interfaceUnion constantSensorFamily)
            (iidRepetition n constantBooleanTranscriptKernel) ∧
          ¬IdentifiesTarget (iidRepetition n constantBooleanTranscriptKernel)
            booleanTarget := by
  have fullInadequate :
      ¬TargetAdequate (interfaceUnion constantSensorFamily) booleanTarget := by
    intro fullAdequate
    have fiberConstant :=
      (target_adequate_iff_fiber_constant
        (interfaceUnion constantSensorFamily) booleanTarget).mp fullAdequate
    apply Bool.false_ne_true
    simpa only [booleanTarget, id_eq] using
      (fiberConstant (x := false) (y := true) rfl)
  have everySubfamily :=
    full_family_inadequacy_persists_to_subfamilies
      constantSensorFamily booleanTarget fullInadequate
  have oneShotFactors :
      KernelFactorsThrough (interfaceUnion constantSensorFamily)
        constantBooleanTranscriptKernel := by
    exact ⟨fun _ => MeasureTheory.diracProba (), rfl⟩
  refine ⟨fullInadequate, ?_, ?_⟩
  · intro selected
    simpa only [subfamilyUnion, interfaceUnion] using everySubfamily selected
  · intro n
    exact ⟨iid_repetition_preserves_factorization
      (interfaceUnion constantSensorFamily) constantBooleanTranscriptKernel n
        oneShotFactors,
      boolean_target_not_identified_by_any_iid_repetition n⟩
#print axioms observation_language_insufficiency_witness

/-- The boxed distinction is a formal nonimplication: repairable budget insufficiency does not
imply that the full observation language is insufficient. -/
theorem budget_insufficiency_does_not_imply_observation_language_insufficiency :
    ¬(BudgetInsufficient budgetSensorFamily booleanTarget ({false} : Set Bool) →
      ObservationLanguageInsufficient budgetSensorFamily booleanTarget) := by
  intro implication
  exact implication budget_insufficiency_witness budget_sensor_full_adequate
#print axioms budget_insufficiency_does_not_imply_observation_language_insufficiency

/- Degenerate audit: an empty interface family cannot recover a nonconstant Boolean target. -/
example :
    ObservationLanguageInsufficient
      ((fun i : Empty => Empty.elim i) :
        InterfaceFamily Empty Bool (fun _ => Unit)) booleanTarget := by
  intro adequate
  have fiberConstant :=
    (target_adequate_iff_fiber_constant
      (interfaceUnion
        ((fun i : Empty => Empty.elim i) :
          InterfaceFamily Empty Bool (fun _ => Unit))) booleanTarget).mp adequate
  apply Bool.false_ne_true
  simpa only [booleanTarget, id_eq] using
    (fiberConstant (x := false) (y := true) rfl)

/- Degenerate audit: the singleton interface family is the language-insufficiency witness. -/
example : ObservationLanguageInsufficient constantSensorFamily booleanTarget :=
  observation_language_insufficiency_witness.1

/- Degenerate audit: selecting the already-full budget family recovers the identity target. -/
example :
    TargetAdequate (subfamilyUnion budgetSensorFamily Set.univ) booleanTarget := by
  refine ⟨fun readings => readings ⟨true, Set.mem_univ true⟩, ?_⟩
  funext state
  simp [booleanTarget, subfamilyUnion, budgetSensorFamily, jointReadout]

/- Degenerate audit: a zero-defect constant target makes both insufficiency notions false. -/
example :
    ¬ObservationLanguageInsufficient
        ((fun i : Empty => Empty.elim i) :
          InterfaceFamily Empty Bool (fun _ => Unit))
        (fun _ : Bool => ()) ∧
      ¬BudgetInsufficient
        ((fun i : Empty => Empty.elim i) :
          InterfaceFamily Empty Bool (fun _ => Unit))
        (fun _ : Bool => ()) (∅ : Set Empty) := by
  have adequate :
      TargetAdequate
        (interfaceUnion
          ((fun i : Empty => Empty.elim i) :
            InterfaceFamily Empty Bool (fun _ => Unit)))
        (fun _ : Bool => ()) := by
    exact ⟨fun _ => (), rfl⟩
  have selectedAdequate :
      TargetAdequate
        (subfamilyUnion
          ((fun i : Empty => Empty.elim i) :
            InterfaceFamily Empty Bool (fun _ => Unit))
          (∅ : Set Empty))
        (fun _ : Bool => ()) := by
    exact ⟨fun _ => (), rfl⟩
  exact ⟨fun inadequate => inadequate adequate,
    fun budgetInsufficient => budgetInsufficient.1 selectedAdequate⟩

/- Degenerate audit: empty and singleton state types need no extra hypothesis. -/
example :
    TargetAdequate
      (interfaceUnion
        ((fun i : Empty => Empty.elim i) :
          InterfaceFamily Empty Empty (fun _ => Unit)))
      ((fun x : Empty => Empty.elim x) : Concept Empty Unit) := by
  refine ⟨fun _ => (), ?_⟩
  funext x
  exact Empty.elim x

example :
    TargetAdequate
      (interfaceUnion
        ((fun i : Empty => Empty.elim i) :
          InterfaceFamily Empty Unit (fun _ => Unit)))
      (id : Concept Unit Unit) := by
  exact ⟨fun _ => (), by funext x; cases x; rfl⟩

/- Degenerate audit: a literal zero map is recoverable even from an empty family. -/
example :
    TargetAdequate
      (interfaceUnion
        ((fun i : Empty => Empty.elim i) :
          InterfaceFamily Empty Bool (fun _ => Unit)))
      (fun _ : Bool => (0 : Nat)) := by
  exact ⟨fun _ => 0, rfl⟩

/- Degenerate audit: zero samples retain the same full-union factorization and failure. -/
example :
    KernelFactorsThrough (interfaceUnion constantSensorFamily)
        (iidRepetition 0 constantBooleanTranscriptKernel) ∧
      ¬IdentifiesTarget (iidRepetition 0 constantBooleanTranscriptKernel)
        booleanTarget :=
  observation_language_insufficiency_witness.2.2 0

end D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.HorizontalSaturationSeparation
