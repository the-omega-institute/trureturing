# Refinement Shrinks Indistinguishability

## Abstract

Factor-map refinement transports fine-readout equality to the coarse readout.

**Theorem 1.1 (Fine equality implies coarse equality).**

$$\begin{gathered}\forall X, C, D: \operatorname{Type},\\{}qC: Concept(X, C), qD: Concept(X, D),\\{}x, y: X,\\{}(\exists p: D \to C, qC = compose(p, qD)) \Rightarrow (qD(x) = qD(y)) \Rightarrow qC(x) = qC(y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/RefinementShrinksIndistinguishability.refinement_shrinks_indistinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concepts C and D are arbitrary readout channels on the same state type. Refinement is the source-defined factorization of the coarse readout through the fine one.

The factor map is applied to equality of the fine readouts. The two factorization equations then identify the resulting values with the coarse readouts.

No surjectivity, finiteness, or effectiveness premise is required; the statement retains the source theorem's full generality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/RefinementShrinksIndistinguishability.refinement_shrinks_indistinguishability`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
