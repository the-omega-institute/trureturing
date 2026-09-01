# Positive Invariant Metric Selection

## Abstract

Zero real drift, unit spectrum, and a positive invariant metric are equivalent.

**Theorem 1.1 (Positive metric selection is equivalent to zero drift).**

$$\begin{gathered}\forall \delta, \gamma, P: \mathbb{R},\\{}0 < P \Rightarrow\\{}\operatorname{let} u: \mathbb{C} = \operatorname{exp}((\delta + i\gamma) \cdot P); \operatorname{let} v: \mathbb{C} = \operatorname{exp}(-((\delta + i\gamma) \cdot P)); \operatorname{let} M: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}) = \operatorname{diagonal}({[u, v]}); \\{}\operatorname{ListTFAE}({[\delta = 0,\\{}\forall \lambda: \mathbb{C}, \lambda \in \operatorname{spectrum}(\mathbb{C}, M), \left\lVert \lambda \right\rVert = 1,\\{}\exists H: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}), \operatorname{PosDef}(H) \land M^{*} \cdot H \cdot M = H]}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/PositiveInvariantMetricSelection.positive_invariant_metric_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two diagonal modes are constructed from real drift, oscillation, and a strictly positive period.

The equivalence retains all three clauses: zero drift, unit norm for every spectral value, and preservation of a positive definite Hermitian metric.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Algebra/PositiveInvariantMetricSelection.positive_invariant_metric_selection`
