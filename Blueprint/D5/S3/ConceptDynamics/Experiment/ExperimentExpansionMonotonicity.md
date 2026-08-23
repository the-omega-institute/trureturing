# Experiment Expansion and Indistinguishability

## Abstract

Expanding the allowed experiments can only shrink state indistinguishability.

**Theorem 1.1 (Experiment expansion shrinks indistinguishability).**

$$\begin{gathered}\forall E, X, R: \operatorname{Type},\\{}original, expanded: \operatorname{Set}\left(E\right),\\{}run: E \to X \to R,\\{}original \subseteq expanded \Rightarrow\\{}\operatorname{experimentIndistinguishability}\left(expanded, run\right) \subseteq \operatorname{experimentIndistinguishability}\left(original, run\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/ExperimentExpansionMonotonicity.expansion_shrinks_indistinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed response map, two states are indistinguishable relative to an allowed experiment set when every experiment in that set returns the same response on both states.

If the original experiments are contained in an expanded set, agreement under every expanded experiment includes agreement under every original one. Thus expansion can remove indistinguishable pairs but cannot create them.

The proof views each relation as a bounded intersection of equal-response sets and applies Mathlib's bounded-intersection inclusion law.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/ExperimentExpansionMonotonicity.expansion_shrinks_indistinguishability`
