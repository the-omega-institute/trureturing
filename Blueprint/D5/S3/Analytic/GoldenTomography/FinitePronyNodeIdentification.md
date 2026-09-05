# Finite Prony Node Identification

## Abstract

A full finite recurrence window identifies every separated Prony node carrying nonzero weight.

**Theorem 1.1 (A finite recurrence window identifies the true spectral roots).**

$$\operatorname{Rec}(q, c) \implies (\forall j, \operatorname{q}(x_{j}) = 0) \land \operatorname{Rec}(\operatorname{A}(x), c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification.finite_prony_node_identification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an m-mode exponential moment sequence with pairwise distinct nodes and nonzero weights, any candidate polynomial whose coefficient recurrence vanishes on the first m shifts must evaluate to zero at every true node. The theorem also records that the genuine node-annihilator recurrence supplies a satisfiable witness.

The proof converts candidate evaluations into residual mode weights. The recurrence says that the first matching moment window of those residual weights is zero, and finite Vandermonde injectivity forces every residual weight to vanish. Nonzero original weights then expose each candidate root.

This is the exact converse layer needed before algorithmic unknown-node Prony recovery. It does not yet select recurrence coefficients, prove uniqueness among monic degree-m candidates, or control root perturbations under noise.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyNodeIdentification.finite_prony_node_identification`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](FinitePronyHankelReconstruction.md)
