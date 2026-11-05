import D5.S3.Topology.Measures.AtlasBoundaryCheck

noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open AtlasFiniteSignedCheck AtlasObservationCheck
open D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
open D5.S3.TotalVariation.Pinsker
namespace AtlasIndependentReview
local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool := by infer_instance

def unequalSigned (b : Bool) : ℝ := if b then -2 else 5

-- Unequal opposite signs leave nonzero residual mass under a many-to-one map.
theorem partial_cancellation :
    (atomic unequalSigned).totalVariation.real univ = 7 ∧
    (SignedMeasure.totalVariation ((atomic unequalSigned).map (fun _ : Bool => ()))).real univ = 3 := by
  constructor
  · rw [full_variation]
    norm_num [atomic_singleton, unequalSigned]
  · rw [full_variation]
    norm_num [atomic_map_singleton, unequalSigned]

def leftWeights (b : Bool) : ℝ := if b then 1/4 else 3/4
def rightWeights (b : Bool) : ℝ := if b then 3/4 else 1/4
def leftLaw : ProbabilityMeasure Bool := lawOfMass
  ⟨leftWeights, by intro b; cases b <;> norm_num [leftWeights], by norm_num [leftWeights]⟩
def rightLaw : ProbabilityMeasure Bool := lawOfMass
  ⟨rightWeights, by intro b; cases b <;> norm_num [rightWeights], by norm_num [rightWeights]⟩

theorem overlapping_probability_test :
    totalVariation (massVector leftLaw) (massVector rightLaw) = 1/2 ∧
    ∃ E : Finset Bool, (leftLaw : Measure Bool).real E +
      (rightLaw : Measure Bool).real (Eᶜ : Finset Bool) = 1/2 := by
  have h : totalVariation (massVector leftLaw) (massVector rightLaw) = 1/2 := by
    rw [show massVector leftLaw = leftWeights from massVector_lawOfMass _,
      show massVector rightLaw = rightWeights from massVector_lawOfMass _]
    norm_num [totalVariation, leftWeights, rightWeights]
  exact ⟨h, by simpa only [h, Finset.coe_compl, show (1:ℝ)-1/2 = 1/2 by norm_num] using
    actual_optimal_test leftLaw rightLaw⟩

-- Full signed variation stays twice the statistical distance for overlapping laws.
theorem overlapping_full_variation :
    ((leftLaw : Measure Bool).toSignedMeasure -
      (rightLaw : Measure Bool).toSignedMeasure).totalVariation.real univ = 1 := by
  rw [probability_variation, overlapping_probability_test.1]
  norm_num

-- The same certified histories can have partial rather than perfect discrimination.
open AtlasBoundaryCheck in
def historyOutput (b : Bool) : Bool :=
  observer.q2 (evolution.recordImage (if b then second else first))

theorem partial_history_discrimination :
    totalVariation (massVector (leftLaw.map historyOutput))
      (massVector (rightLaw.map historyOutput)) = 1/2 := by
  rw [massVector_map, massVector_map]
  rw [show massVector leftLaw = leftWeights from massVector_lawOfMass _,
    show massVector rightLaw = rightWeights from massVector_lawOfMass _]
  have hout : historyOutput = Bool.not := by
    funext b
    cases b <;> rfl
  rw [hout]
  norm_num [D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass,
    totalVariation, leftWeights, rightWeights]

-- A fifth label is within the source reconstruction scope; no three-label strengthening.
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

theorem five_label_joint_reconstruction :
    jointKernel (deletionReadout (Finset.univ : Finset (Fin 5))) =
      D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.diagonal (SupportedCircle (Finset.univ : Finset (Fin 5))) :=
  (deletion_joint_kernel_iff (Finset.univ : Finset (Fin 5)) (by decide)).mpr (by decide)

#print axioms partial_cancellation
#print axioms overlapping_probability_test
#print axioms overlapping_full_variation
#print axioms partial_history_discrimination
#print axioms five_label_joint_reconstruction
end AtlasIndependentReview
