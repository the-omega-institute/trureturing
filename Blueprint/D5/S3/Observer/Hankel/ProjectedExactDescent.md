# Exact Descent Persists at Every Time

## Abstract

Global exact descent propagates through every driven time step and preserves outputs that factor through the projection.

**Theorem 1.1 (Exact projected states at every time).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedExactDescent.projectedState_eq_of_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedExactDescent.projectedState_eq_of_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The global operator identity P A=A_r P, together with the constructed reduced input P B, gives equality between every projected full state and reduced state. Both initial states are zero. This is a forced-input application of exact descent, and needs no contraction assumption.

**Theorem 1.2 (All factorized outputs are preserved).**

Lean statement: `D5/S3/Observer/Hankel/ProjectedExactDescent.outputs_eq_of_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/ProjectedExactDescent.outputs_eq_of_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the output also factors through P, exact descent preserves every output at every time. Full-state leakage can remain nonzero. Consequently a fixed global one-step exact descent cannot later fail solely because of hidden leakage. A one-trajectory check or a changing interface would require different hypotheses.

## References

- Truth anchor: `D5/S3/Observer/Hankel/ProjectedExactDescent.outputs_eq_of_descent`
- Truth anchor: `D5/S3/Observer/Hankel/ProjectedExactDescent.projectedState_eq_of_descent`
- Dependency: [D5/S3/Observer/Hankel/ProjectedRealizationError](ProjectedRealizationError.md)
