# Cayley transforms and resolvent increments

## Abstract

Cayley transport and endpoint resolvent bounds on the Hermitian matrix interval.

**Definition 1.1 (Real-parameter resolvent).**

Lean statement: `D5/S3/Quantum/Matrix/CayleyResolvent.resolvent`

*Formalization.* `D5/S3/Quantum/Matrix/CayleyResolvent.resolvent` (`✓ std3`).

*Citation.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

For a real scalar s and a finite complex square matrix A, define R_s(A)=(sI−A) inverse. The definition uses Mathlib's nonsingular inverse; the endpoint theorem requires positive definite denominators.

**Theorem 1.2 (Inverse reverses positive order).**

Lean statement: `D5/S3/Quantum/Matrix/CayleyResolvent.inverse_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CayleyResolvent.inverse_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every dimension and positive definite complex matrices P,Q with P≤Q, one has Q inverse≤P inverse. The comparison is the existing inverse antitonicity theorem on the strictly positive cone.

**Theorem 1.3 (Uniform endpoint factors).**

Lean statement: `D5/S3/Quantum/Matrix/CayleyResolvent.endpoint_resolvent_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CayleyResolvent.endpoint_resolvent_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every dimension, let s≥2, U≤V, and suppose I+U, I−U and I−V are positive definite. Put H=V−U. There is Z_U with R_s(V)−R_s(U)=R_s(U) Z_U R_s(U) and H≤Z_U≤3H. There is Z_V with R_s(V)−R_s(U)=R_s(V) Z_V R_s(V) and H/3≤Z_V≤H. The factors may differ. The first is H+H R_s(V) H. The second is H^(1/2)(I+H^(1/2) R_s(V) H^(1/2)) inverse H^(1/2). Mathlib's Woodbury identity establishes the second factorization without assuming H invertible. Both bounds use positive matrix order and include singular increments.

**Definition 1.4 (Cayley map).**

Lean statement: `D5/S3/Quantum/Matrix/CayleyResolvent.cayley`

*Formalization.* `D5/S3/Quantum/Matrix/CayleyResolvent.cayley` (`✓ std3`).

*Citation.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

Define h(A)=I−2(A+I) inverse on finite complex square matrices. On positive definite matrices this is the usual matrix Cayley transform associated with (t−1)/(t+1).

**Theorem 1.5 (Order-preserving Cayley transport).**

Lean statement: `D5/S3/Quantum/Matrix/CayleyResolvent.cayley_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CayleyResolvent.cayley_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive definite A, both I+h(A) and I−h(A) are positive definite. For every positive definite B with A≤B, one has h(A)≤h(B). The proof reuses Mathlib's inverse order inequality. Positivity of I+h(A) follows from the commuting positive definite product A(A+I) inverse.

**Theorem 1.6 (Resolvent of a Cayley image).**

Lean statement: `D5/S3/Quantum/Matrix/CayleyResolvent.cayley_resolvent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CayleyResolvent.cayley_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive definite A and every real s≥2, R_s(h(A))=(A+I)((s−1)A+(s+1)I) inverse. Both denominator matrices are positive definite. Exact multiplication establishes the inverse identity. The parameters s=2,3,4 give the three rational summands used by the Czerwińska–Franco–Merino counterexample.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CayleyResolvent.cayley`
- Truth anchor: `D5/S3/Quantum/Matrix/CayleyResolvent.cayley_resolvent`
- Truth anchor: `D5/S3/Quantum/Matrix/CayleyResolvent.cayley_transport`
- Truth anchor: `D5/S3/Quantum/Matrix/CayleyResolvent.endpoint_resolvent_factors`
- Truth anchor: `D5/S3/Quantum/Matrix/CayleyResolvent.inverse_antitone`
- Truth anchor: `D5/S3/Quantum/Matrix/CayleyResolvent.resolvent`
