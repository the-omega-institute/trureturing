# Replay of complete neighborhood queries

## Abstract

Complete neighborhood transcripts on finite named simple graphs.

**Theorem 1.1 (Edge inclusion and degree saturation characterize replay).**

Lean statement: `D5/S3/Combinatorics/Graph/CompleteNeighborhoodHistory.history_eq_iff_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CompleteNeighborhoodHistory.history_eq_iff_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G and H be simple graphs on the same finite vertex set. A fixed deterministic adaptive protocol queries labelled vertices and receives their complete unordered neighbor sets. In the run on H, let F be the graph of all edges returned by the replies.

The run on G has exactly the transcript of the run on H if and only if G contains F and, at every recorded query, the degree in G is at most the number of neighbors in that reply. The degree comparison occurs only at labels queried in the actual run on H.

For a candidate containing F, the first recorded neighbor set is contained in the corresponding set in G. Its finite cardinality saturates the upper bound, so the first reply agrees. Induction through the same continuation after that reply gives the complete transcript. Conversely, identical recorded replies supply the edges and the degree bounds.

For a distribution supported on graphs with the same degree as H at each named vertex, the transcript event coincides with the event that every returned edge is present. Conditioning on a positive-mass transcript is therefore conditioning on that edge-extension event.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CompleteNeighborhoodHistory.history_eq_iff_extension`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../../ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.md)
