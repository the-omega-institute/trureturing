/- GID: D5/S3/ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentBoundary/FinitePrefixInfiniteCompletionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equivalent finite-prefix laws coexist with mutually singular completed laws. -/

import D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.MeasureTheory.Measure.MutuallySingular

/- Library-search audit trail (2026-08-26):
   * The exact current-tree search found the frozen Bernoulli observation system
     `InfiniteIdentificationFiniteInexactness`, including its canonical `marginal`,
     `productLaw`, `stateLaw`, `finiteTranscript`, and `distinguishingEvent` objects.
     Its public theorem gives coordinate equivalence and a measurable zero/one event,
     but does not state mutual absolute continuity of every mapped finite-prefix law
     or completed-law mutual singularity, so it is imported rather than wrapped.
   * Exact pinned-Mathlib hits `Measure.map_infinitePi_infinitePi_of_inj`,
     `Measure.infinitePi_eq_pi`, and `Measure.pi_singleton` identify each finite-prefix
     law with its finite product and prove full support. `Measure.MutuallySingular` is
     used directly for the completed-law clause.
   * Body-shape searches found no existing definition of the mapped finite-prefix law;
     the public theorem therefore states the canonical map expression directly and
     introduces no sibling definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentBoundary.FinitePrefixInfiniteCompletionSeparation

open MeasureTheory ProbabilityTheory Set Finset
open D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness

private theorem marginal_singleton_pos
    (p : unitInterval) (hp0 : 0 < (p : Real)) (hp1 : (p : Real) < 1)
    (outcome : Bool) : 0 < marginal p {outcome} := by
  cases outcome with
  | false =>
      rw [marginal, bernoulliMeasure_apply_of_notMem_of_mem p
        (measurableSet_singleton false) (by decide) (by decide)]
      rw [ENNReal.coe_pos, ← NNReal.coe_pos]
      change 0 < 1 - (p : Real)
      linarith
  | true =>
      rw [marginal, bernoulliMeasure_apply_of_mem_of_notMem p
        (measurableSet_singleton true) (by decide) (by decide)]
      rw [ENNReal.coe_pos, ← NNReal.coe_pos]
      exact hp0

private theorem finite_product_absolutelyContinuous
    {Index : Type*} [Fintype Index]
    (p q : unitInterval) (hq0 : 0 < (q : Real)) (hq1 : (q : Real) < 1) :
    Measure.pi (fun _ : Index => marginal p) ≪
      Measure.pi (fun _ : Index => marginal q) := by
  refine Measure.AbsolutelyContinuous.mk fun event _hmeasurable hzero => ?_
  have hempty : event = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro transcript htranscript
    have hsingletonZero :
        Measure.pi (fun _ : Index => marginal q) {transcript} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr htranscript) hzero
    rw [Measure.pi_singleton] at hsingletonZero
    have hnonzero :
        (∏ i, marginal q {transcript i}) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        (marginal_singleton_pos q hq0 hq1 (transcript i)).ne'
    exact hnonzero hsingletonZero
  simp [hempty]

private theorem finite_prefix_law_eq_pi (p : unitInterval) (m : Nat) :
    Measure.map (finiteTranscript m) (productLaw p) =
      Measure.pi (fun _ : Fin m => marginal p) := by
  have hMap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Nat => marginal p)
    (f := fun i : Fin m => (i : Nat)) Fin.val_injective
  calc
    Measure.map (finiteTranscript m) (productLaw p) =
        Measure.infinitePi (fun _ : Fin m => marginal p) := by
      rw [productLaw]
      rw [show finiteTranscript m =
        (fun transcript i => transcript (i : Nat)) by rfl]
      exact hMap
    _ = Measure.pi (fun _ : Fin m => marginal p) :=
      Measure.infinitePi_eq_pi (fun _ : Fin m => marginal p)

/-- The frozen two-state Bernoulli observation system has mutually absolutely
continuous laws on every finite prefix, while its completed transcript laws are
mutually singular. -/
theorem finite_prefix_infinite_completion_separation :
    (∀ m : Nat,
      Measure.map (finiteTranscript m) (stateLaw false) ≪
          Measure.map (finiteTranscript m) (stateLaw true) ∧
        Measure.map (finiteTranscript m) (stateLaw true) ≪
          Measure.map (finiteTranscript m) (stateLaw false)) ∧
      stateLaw false ⟂ₘ stateLaw true := by
  constructor
  · intro m
    simp only [stateLaw]
    rw [finite_prefix_law_eq_pi, finite_prefix_law_eq_pi]
    exact ⟨
      finite_product_absolutelyContinuous lowerBias upperBias
        (by norm_num [upperBias]) (by norm_num [upperBias]),
      finite_product_absolutelyContinuous upperBias lowerBias
        (by norm_num [lowerBias]) (by norm_num [lowerBias])⟩
  · rcases infinite_identification_not_finite_exact_tomography with
      ⟨_, _, hMeasurable, hLower, hUpper, _⟩
    refine ⟨distinguishingEvent, hMeasurable, hLower, ?_⟩
    rw [measure_compl hMeasurable (measure_ne_top _ _), hUpper, measure_univ]
    simp

#print axioms finite_prefix_infinite_completion_separation

end D5.S3.ConceptDynamics.ExperimentBoundary.FinitePrefixInfiniteCompletionSeparation
