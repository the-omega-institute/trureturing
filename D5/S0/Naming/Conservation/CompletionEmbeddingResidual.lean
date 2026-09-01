/- GID: D5/S0/Naming/Conservation/CompletionEmbeddingResidual
   generality: G
   mirror-B: D5/B/S0/Naming/Conservation/CompletionEmbeddingResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The completion image is meagre and its complement has full measure. -/

import D5.S0.Naming.CompletionEmbeddingDense
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Perfect

/-!
This theorem discharges clauses (ii) and (iii) of the source theorem. Clause (i) is already
carried by the frozen `CompletionEmbeddingDense`. Coverage of the residual atom is NOT claimed
here, and ticket D5-T0032 remains OPEN because the existing formalization receipt is misbound
and may only be corrected through the receipt-correction door.

Provenance: repo-derived.
-/

namespace D5.S0.Naming.Conservation.CompletionEmbeddingResidual

open MeasureTheory Topology

set_option checkBinderAnnotations false in
/-- A countable metric space without isolated points has a negligible completion image. -/
theorem completion_embedding_residual_full_measure
    {N : Type*} [MetricSpace N] [Countable N] [PerfectSpace N]
    [MeasurableSpace (UniformSpace.Completion N)]
    (mu : Measure (UniformSpace.Completion N)) [NoAtoms mu] [IsProbabilityMeasure mu] :
    DenseRange ((↑) : N -> UniformSpace.Completion N) ∧
      PerfectSpace (UniformSpace.Completion N) ∧
      IsMeagre (Set.range ((↑) : N -> UniformSpace.Completion N)) ∧
      mu (Set.range ((↑) : N -> UniformSpace.Completion N))ᶜ = 1 := by
  let coeCompletion : N -> UniformSpace.Completion N := (↑)
  have hdense : DenseRange coeCompletion :=
    D5.S0.Naming.CompletionEmbeddingDense.completion_embedding_dense
  have hpreperfect : Preperfect (Set.range coeCompletion) := by
    rw [preperfect_iff_nhds]
    rintro _ ⟨x, rfl⟩ U hU
    have hpreimage : coeCompletion ⁻¹' U ∈ 𝓝 x :=
      (UniformSpace.Completion.continuous_coe (α := N)).continuousAt hU
    obtain ⟨y, ⟨hyU, -⟩, hyx⟩ :=
      preperfect_iff_nhds.mp PerfectSpace.univ_preperfect x (Set.mem_univ x)
        (coeCompletion ⁻¹' U) hpreimage
    refine ⟨coeCompletion y, ⟨hyU, ⟨y, rfl⟩⟩, ?_⟩
    exact fun h => hyx (UniformSpace.Completion.coe_injective (α := N) h)
  have hperfect : Perfect (Set.univ : Set (UniformSpace.Completion N)) := by
    rw [← hdense.closure_eq]
    exact hpreperfect.perfect_closure
  let perfectCompletion : PerfectSpace (UniformSpace.Completion N) :=
    ⟨hperfect.acc⟩
  letI : PerfectSpace (UniformSpace.Completion N) := perfectCompletion
  have hsingle : ∀ x : N,
      IsMeagre ({coeCompletion x} : Set (UniformSpace.Completion N)) := by
    intro x
    apply IsNowhereDense.isMeagre
    rw [isClosed_singleton.isNowhereDense_iff]
    exact interior_singleton _
  have hmeagre : IsMeagre (Set.range coeCompletion) := by
    have h := isMeagre_iUnion hsingle
    simpa only [Set.iUnion_singleton_eq_range] using h
  have hnull : mu (Set.range coeCompletion) = 0 := by
    exact @Set.Countable.measure_zero _ _ (Set.range coeCompletion)
      (Set.countable_range coeCompletion) mu
      (by assumption)
  have hfull : mu (Set.range coeCompletion)ᶜ = 1 := by
    have h := measure_of_measure_compl_eq_zero
      (μ := mu) (s := (Set.range coeCompletion)ᶜ) (by simpa using hnull)
    simpa using h
  exact ⟨hdense, perfectCompletion, hmeagre, hfull⟩

end D5.S0.Naming.Conservation.CompletionEmbeddingResidual
