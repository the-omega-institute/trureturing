/- GID: D5/S0/Naming/CompletionEmbeddingDense
   generality: G
   mirror-B: D5/B/S0/Naming/CompletionEmbeddingDense
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical map into a metric completion has dense range. -/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Completion

namespace D5.S0.Naming.CompletionEmbeddingDense

/-- The canonical map from a metric space into its completion has dense range. -/
theorem completion_embedding_dense {N : Type*} [MetricSpace N] :
    DenseRange ((↑) : N -> UniformSpace.Completion N) :=
  UniformSpace.Completion.denseRange_coe

/-- The metric-space hypothesis and its domain are jointly inhabited. -/
example : MetricSpace Unit := inferInstance

/-- A concrete inhabitant of the witnessed metric-space domain. -/
example : Unit := ()

/-- The wrapper applies to a concrete inhabited metric space. -/
example : DenseRange ((↑) : Unit -> UniformSpace.Completion Unit) :=
  completion_embedding_dense

end D5.S0.Naming.CompletionEmbeddingDense
