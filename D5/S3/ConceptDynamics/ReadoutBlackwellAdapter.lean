/- GID: D5/S3/ConceptDynamics/ReadoutBlackwellAdapter
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ReadoutBlackwellAdapter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Measurable readout factorization becomes deterministic Blackwell garbling and Bayes-risk monotonicity. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.Estimation.DecisionRisk.GarblingIncreasesBayesRisk

/- Library-search audit trail (2026-09-01):
   * `ConceptJoinUniversal` supplies the repository factorization preorder on
     readouts. `GarblingIncreasesBayesRisk` supplies the existing kernel-level
     Blackwell order and its Bayes-risk theorem.
   * Pinned Mathlib supplies deterministic Markov kernels and the exact
     composition law for two deterministic kernels.
   * Repository searches found no theorem transporting measurable readout
     factorization into the existing Blackwell order. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ReadoutBlackwellAdapter

open MeasureTheory ProbabilityTheory
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.Estimation.DecisionRisk.GarblingIncreasesBayesRisk
open scoped ENNReal

/-- Measurable refinement records the same factorization as `Refines`, together
with the measurability needed to form a deterministic garbling kernel. -/
def MeasurableRefines
    {X C D : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSpace D]
    (q_C : Concept X C) (q_D : Concept X D) : Prop :=
  ∃ factor : D -> C, Measurable factor /\ q_C = factor ∘ q_D

/-- Forgetting measurability recovers the repository's ordinary refinement
preorder. -/
theorem measurableRefines_refines
    {X C D : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSpace D]
    {q_C : Concept X C} {q_D : Concept X D}
    (refinement : MeasurableRefines q_C q_D) :
    Refines q_C q_D := by
  rcases refinement with ⟨factor, _measurable, factorization⟩
  exact ⟨factor, factorization⟩

/-- A measurable factorization of a coarse readout through a finer readout is
exactly a deterministic Blackwell garbling in the expected direction. -/
theorem measurable_refinement_blackwell
    {X C D : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSpace D]
    (q_C : Concept X C) (q_D : Concept X D)
    (measurableC : Measurable q_C) (measurableD : Measurable q_D)
    (refinement : MeasurableRefines q_C q_D) :
    BlackwellDominates
      (Kernel.deterministic q_D measurableD)
      (Kernel.deterministic q_C measurableC) := by
  rcases refinement with ⟨factor, measurableFactor, factorization⟩
  refine ⟨Kernel.deterministic factor measurableFactor, inferInstance, ?_⟩
  subst q_C
  simpa using
    (Kernel.deterministic_comp_deterministic
      (f := q_D) (g := factor) measurableD measurableFactor).symm

/-- Every decision problem has weakly smaller optimal Bayes risk after the finer
measurable readout than after its deterministic postprocessing. -/
theorem bayesRisk_mono_of_measurable_refinement
    {X C D Action : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSpace D]
    [MeasurableSpace Action]
    (q_C : Concept X C) (q_D : Concept X D)
    (measurableC : Measurable q_C) (measurableD : Measurable q_D)
    (refinement : MeasurableRefines q_C q_D)
    (loss : X -> Action -> ENNReal) (prior : Measure X) :
    bayesRisk loss (Kernel.deterministic q_D measurableD) prior <=
      bayesRisk loss (Kernel.deterministic q_C measurableC) prior := by
  exact bayesRisk_le_of_blackwellDominates _ _
    (measurable_refinement_blackwell q_C q_D measurableC measurableD refinement)
    loss prior

#print axioms measurable_refinement_blackwell
#print axioms bayesRisk_mono_of_measurable_refinement

end D5.S3.ConceptDynamics.ReadoutBlackwellAdapter
