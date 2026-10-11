import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory LeanInformationAudit
open scoped ENNReal

abbrev wordSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Letter → ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def wordArena : Arena where
  signature := wordSignature
  Law R := ∀ F : CommonFlow, F.C ∘ₘ F.nuP = F.nuP ∧
    (∀ᵐ Q ∂F.nuP, ∀ n i, R.readout () F Q n i =
      iterate F.L (coordinate 0 i) n Q) ∧
    (∀ᵐ Q ∂F.nuP, R.readout () F Q 0 1 =
      (1 - u Q) * ∫⁻ W, (1 - v W) ∂F.B Q)

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ _ Q n i => coordinate n i Q) (fun e => nomatch e)
def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

theorem word_bridge : (type_of% (@common_flow_word_iteration)) ↔ wordArena.Law wordActual := by
  rfl

theorem word_positive : wordArena.Law wordActual := common_flow_word_iteration

abbrev boundsSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def boundsArena : Arena where
  signature := boundsSignature
  Law R := ∀ F : CommonFlow,
    (∀ Q, (1 / 5 : ℝ≥0∞) • F.C Q ≤ F.L Q ∧
      F.L Q ≤ (4 / 15 : ℝ≥0∞) • F.C Q) ∧
    (∀ᵐ Q ∂F.nuP, endpointCompletion ≤ R.readout () F Q ∧
      R.readout () F Q ≤ (4 / 9 : ℝ≥0∞) ∧
      iterate F.L (R.readout () F) 3 Q ≤ endpointCompletion * endpointRate ^ 3)

def boundsActual : Realization boundsSignature :=
  realize boundsSignature (fun _ _ Q => g Q) (fun e => nomatch e)
def boundsRejected : Realization boundsSignature :=
  realize boundsSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem bounds_bridge : (type_of% (@common_flow_operator_bounds)) ↔
    boundsArena.Law boundsActual := Iff.rfl

theorem bounds_positive : boundsArena.Law boundsActual := common_flow_operator_bounds

abbrev normalizedSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def normalizedArena : Arena where
  signature := normalizedSignature
  Law R := ∀ F : CommonFlow,
    ∀ᵐ Q ∂F.nuP, R.readout () F Q ≤ endpointCompletion

def normalizedActual : Realization normalizedSignature :=
  realize normalizedSignature (fun _ F Q => normalizedIterate F g 3 Q) (fun e => nomatch e)
def normalizedRejected : Realization normalizedSignature :=
  realize normalizedSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem normalized_bridge : (type_of% (@common_flow_normalized_third_step)) ↔
    normalizedArena.Law normalizedActual := Iff.rfl

theorem normalized_positive : normalizedArena.Law normalizedActual :=
  common_flow_normalized_third_step

abbrev defectSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def defectArena : Arena where
  signature := defectSignature
  Law R := ∀ F : CommonFlow,
    ∀ᵐ Q ∂F.nuP, 0 ≤ R.readout () F Q

def defectActual : Realization defectSignature :=
  realize defectSignature (fun _ F Q => threeStepDefect F Q) (fun e => nomatch e)
def defectRejected : Realization defectSignature :=
  realize defectSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem defect_bridge : (type_of% (@common_flow_three_step_defect_nonneg)) ↔
    defectArena.Law defectActual := Iff.rfl

theorem defect_positive : defectArena.Law defectActual :=
  common_flow_three_step_defect_nonneg

abbrev coreSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor ⊕ BDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def coreArena : Arena where
  signature := coreSignature
  Law R := ∀ F : CommonFlow, ∃ (P : Set PDescriptor) (S : Set BDescriptor),
    MeasurableSet P ∧ MeasurableSet S ∧
    (∀ᵐ Q ∂F.nuP, Q ∈ P) ∧ (∀ᵐ W ∂F.nuB, W ∈ S) ∧
    (∀ Q ∈ P, R.readout () F (.inl Q) ∧ ∀ᵐ W ∂F.B Q, W ∈ S) ∧
    (∀ W ∈ S, R.readout () F (.inr W) ∧ ∀ᵐ Q ∂F.A W, Q ∈ P)

def coreActual : Realization coreSignature :=
  realize coreSignature (fun _ F x => Sum.elim (goodP F) (goodB F) x) (fun e => nomatch e)
def coreRejected : Realization coreSignature :=
  realize coreSignature (fun _ _ _ => False) (fun e => nomatch e)

theorem core_bridge : (type_of% (@common_flow_conull_core)) ↔
    coreArena.Law coreActual := Iff.rfl

theorem core_positive : coreArena.Law coreActual := common_flow_conull_core


def wordRecord (hv : ∃ bad : Realization wordSignature, ¬ wordArena.Law bad)
    (hs : Sensitivity wordArena wordActual)
    (hd : ObservationalDependence wordSignature wordActual) :
    Registration wordArena (type_of% (@common_flow_word_iteration)) where
  actual := wordActual
  bridge := word_bridge
  variation := ⟨word_positive, hv⟩
  sensitivity := hs
  dependence := hd

def boundsRecord (hv : ∃ bad : Realization boundsSignature, ¬ boundsArena.Law bad)
    (hs : Sensitivity boundsArena boundsActual)
    (hd : ObservationalDependence boundsSignature boundsActual) :
    Registration boundsArena (type_of% (@common_flow_operator_bounds)) where
  actual := boundsActual
  bridge := bounds_bridge
  variation := ⟨bounds_positive, hv⟩
  sensitivity := hs
  dependence := hd

def coreRecord (hv : ∃ bad : Realization coreSignature, ¬ coreArena.Law bad)
    (hs : Sensitivity coreArena coreActual)
    (hd : ObservationalDependence coreSignature coreActual) :
    Registration coreArena (type_of% (@common_flow_conull_core)) where
  actual := coreActual
  bridge := core_bridge
  variation := ⟨core_positive, hv⟩
  sensitivity := hs
  dependence := hd

def normalizedRecord (hv : ∃ bad : Realization normalizedSignature, ¬ normalizedArena.Law bad)
    (hs : Sensitivity normalizedArena normalizedActual)
    (hd : ObservationalDependence normalizedSignature normalizedActual) :
    Registration normalizedArena (type_of% (@common_flow_normalized_third_step)) where
  actual := normalizedActual
  bridge := normalized_bridge
  variation := ⟨normalized_positive, hv⟩
  sensitivity := hs
  dependence := hd

def defectRecord (hv : ∃ bad : Realization defectSignature, ¬ defectArena.Law bad)
    (hs : Sensitivity defectArena defectActual)
    (hd : ObservationalDependence defectSignature defectActual) :
    Registration defectArena (type_of% (@common_flow_three_step_defect_nonneg)) where
  actual := defectActual
  bridge := defect_bridge
  variation := ⟨defect_positive, hv⟩
  sensitivity := hs
  dependence := hd

abbrev normalizedStepParams :=
  CommonFlow × ((PDescriptor → ℝ≥0∞) × ℕ)

abbrev normalizedStepSignature : Signature where
  Params := normalizedStepParams
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def normalizedStepArena : Arena where
  signature := normalizedStepSignature
  Law R := ∀ (F : CommonFlow) (f : PDescriptor → ℝ≥0∞),
    Measurable f → ∀ (n : ℕ) (Q : PDescriptor),
      normalizedIterate F f (n + 1) Q =
        R.readout () (F, (f, n)) Q

def normalizedStepActual : Realization normalizedStepSignature :=
  realize normalizedStepSignature
    (fun _ p Q => normalizedAction p.1 (normalizedIterate p.1 p.2.1 p.2.2) Q)
    (fun e => nomatch e)

def normalizedStepRejected : Realization normalizedStepSignature :=
  realize normalizedStepSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem normalizedStep_bridge :
    (type_of% (@normalizedIterate_succ)) ↔ normalizedStepArena.Law normalizedStepActual :=
  Iff.rfl

theorem normalizedStep_positive : normalizedStepArena.Law normalizedStepActual := by
  intro F f hf n Q
  exact normalizedIterate_succ F f hf n Q

def normalizedStepRecord
    (hv : ∃ bad : Realization normalizedStepSignature,
      ¬ normalizedStepArena.Law bad)
    (hs : Sensitivity normalizedStepArena normalizedStepActual)
    (hd : ObservationalDependence normalizedStepSignature normalizedStepActual) :
    Registration normalizedStepArena (type_of% (@normalizedIterate_succ)) where
  actual := normalizedStepActual
  bridge := normalizedStep_bridge
  variation := ⟨normalizedStep_positive, hv⟩
  sensitivity := hs
  dependence := hd

abbrev actionAddParams :=
  CommonFlow × ((PDescriptor → ℝ≥0∞) × (PDescriptor → ℝ≥0∞))

abbrev actionAddSignature : Signature where
  Params := actionAddParams
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actionAddArena : Arena where
  signature := actionAddSignature
  Law R := ∀ (F : CommonFlow) (f₁ f₂ : PDescriptor → ℝ≥0∞),
    Measurable f₁ → ∀ Q : PDescriptor,
      R.readout () (F, (f₁, f₂)) Q =
        normalizedAction F f₁ Q + normalizedAction F f₂ Q

def actionAddActual : Realization actionAddSignature :=
  realize actionAddSignature
    (fun _ p Q => normalizedAction p.1 (fun R => p.2.1 R + p.2.2 R) Q)
    (fun e => nomatch e)

def actionAddRejected : Realization actionAddSignature :=
  realize actionAddSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem actionAdd_bridge :
    (type_of% (@normalizedAction_add)) ↔ actionAddArena.Law actionAddActual :=
  Iff.rfl

theorem actionAdd_positive : actionAddArena.Law actionAddActual := by
  intro F f₁ f₂ hf₁ Q
  exact normalizedAction_add F f₁ f₂ hf₁ Q

def actionAddRecord
    (hv : ∃ bad : Realization actionAddSignature,
      ¬ actionAddArena.Law bad)
    (hs : Sensitivity actionAddArena actionAddActual)
    (hd : ObservationalDependence actionAddSignature actionAddActual) :
    Registration actionAddArena (type_of% (@normalizedAction_add)) where
  actual := actionAddActual
  bridge := actionAdd_bridge
  variation := ⟨actionAdd_positive, hv⟩
  sensitivity := hs
  dependence := hd

abbrev averageSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def averageArena : Arena where
  signature := averageSignature
  Law R := ∀ (F : CommonFlow) (Q : PDescriptor),
    R.readout () F Q =
      (normalizedIterate F g 1 Q + normalizedIterate F g 2 Q +
        normalizedIterate F g 3 Q) / 3

def averageActual : Realization averageSignature :=
  realize averageSignature (fun _ F Q =>
    normalizedAction F (fun R => threeStepAverage F R) Q) (fun e => nomatch e)

def averageRejected : Realization averageSignature :=
  realize averageSignature (fun _ _ => 0) (fun e => nomatch e)

theorem average_bridge :
    (type_of% (@normalizedAction_threeStepAverage)) ↔ averageArena.Law averageActual :=
  Iff.rfl

theorem average_positive : averageArena.Law averageActual := by
  intro F Q
  exact normalizedAction_threeStepAverage F Q

def averageRecord
    (hv : ∃ bad : Realization averageSignature, ¬ averageArena.Law bad)
    (hs : Sensitivity averageArena averageActual)
    (hd : ObservationalDependence averageSignature averageActual) :
    Registration averageArena (type_of% (@normalizedAction_threeStepAverage)) where
  actual := averageActual
  bridge := average_bridge
  variation := ⟨average_positive, hv⟩
  sensitivity := hs
  dependence := hd

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail

abbrev coordinateMeasurableSignature : Signature where
  Params := ℕ × Letter
  State _ := PDescriptor
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateMeasurableActual : Realization coordinateMeasurableSignature :=
  realize _ (fun _ p Q => coordinate p.1 p.2 Q) (fun e => nomatch e)

def coordinateMeasurableArena : Arena where
  signature := coordinateMeasurableSignature
  Law R := ∀ n i, Measurable (R.readout 0 (n, i))

theorem coordinateMeasurable_bridge : (type_of% (@measurable_coordinate)) ↔
    coordinateMeasurableArena.Law coordinateMeasurableActual := Iff.rfl

theorem coordinateMeasurable_actual_law : coordinateMeasurableArena.Law coordinateMeasurableActual :=
  coordinateMeasurable_bridge.mp measurable_coordinate

abbrev iterateMeasurableSignature : Signature where
  Params := CommonFlow × (PDescriptor → ℝ≥0∞) × ℕ
  State _ := PDescriptor
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def iterateMeasurableActual : Realization iterateMeasurableSignature :=
  realize _ (fun _ p Q => iterate p.1.L p.2.1 p.2.2 Q) (fun e => nomatch e)

def iterateMeasurableArena : Arena where
  signature := iterateMeasurableSignature
  Law R := ∀ F f, Measurable f → ∀ n, Measurable (R.readout 0 (F, f, n))

theorem iterateMeasurable_bridge : (type_of% (@measurable_iterate)) ↔
    iterateMeasurableArena.Law iterateMeasurableActual := Iff.rfl

theorem iterateMeasurable_actual_law : iterateMeasurableArena.Law iterateMeasurableActual :=
  iterateMeasurable_bridge.mp measurable_iterate

abbrev weightedIntegralSignature : Signature where
  Params := CommonFlow × (PDescriptor → ℝ≥0∞)
  State _ := PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def weightedIntegralActual : Realization weightedIntegralSignature :=
  realize _ (fun i p Q => if i = 0 then ∫⁻ Q', p.2 Q' ∂p.1.L Q else (1 - u Q) * ∫⁻ W, v W * ∫⁻ Q', p.2 Q' ∂p.1.A W ∂p.1.B Q) (fun e => nomatch e)

def weightedIntegralArena : Arena where
  signature := weightedIntegralSignature
  Law R := ∀ F f, Measurable f → ∀ Q, R.readout 0 (F, f) Q = R.readout 1 (F, f) Q

theorem weightedIntegral_bridge : (type_of% (@L_integral)) ↔
    weightedIntegralArena.Law weightedIntegralActual := Iff.rfl

theorem weightedIntegral_actual_law : weightedIntegralArena.Law weightedIntegralActual :=
  weightedIntegral_bridge.mp L_integral

structure PartitionParameters where
  source : ActivePhase
  target : ActivePhase
  prepend : ValidTail source → ValidTail target
  stop : ValidTail target
  measure : Measure (ValidTail target)

abbrev partitionSignature : Signature where
  Params := PartitionParameters
  State _ := Unit
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Measure (ValidTail p.target)
  Anchor := Empty
  finiteAnchor := inferInstance

def partitionActual : Realization partitionSignature :=
  realize _ (fun i p _ => if i = 0 then p.measure else
    p.measure {p.stop} • Measure.dirac p.stop + (p.measure.comap p.prepend).map p.prepend)
    (fun e => nomatch e)

def partitionArena : Arena where
  signature := partitionSignature
  Law R := ∀ (s t : ActivePhase) (f : ValidTail s → ValidTail t), MeasurableEmbedding f →
    ∀ (a : ValidTail t), (∀ x, f x ≠ a) → (∀ y, y = a ∨ ∃ x, y = f x) →
    ∀ D : Measure (ValidTail t),
      R.readout 0 ⟨s, t, f, a, D⟩ () = R.readout 1 ⟨s, t, f, a, D⟩ ()

theorem partition_bridge : (type_of% (@partition_reconstruct)) ↔
    partitionArena.Law partitionActual := Iff.rfl

theorem partition_actual_law : partitionArena.Law partitionActual :=
  partition_bridge.mp partition_reconstruct

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
