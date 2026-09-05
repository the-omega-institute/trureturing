# Finite Prony-Hankel Reconstruction

## Abstract

Separated finite exponential modes satisfy an annihilating recurrence and have full-rank Hankel sections.

**Theorem 1.1 (Separated finite exponential modes have exact Prony recurrence and Hankel rank).**

$$\operatorname{Rec}(\operatorname{A}(x), c) \land \operatorname{H}(c) = \operatorname{V}(x)\cdot\operatorname{D}(w)\cdot\operatorname{V}(x)^{T} \land \operatorname{Injective}(\operatorname{M}(x)) \land \operatorname{rank}(\operatorname{H}(c)) = m$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction.finite_prony_hankel_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of nodes and weights, the theorem packages the node-annihilator recurrence, the Vandermonde-diagonal-Vandermonde-transpose factorization of every Hankel section, injective recovery of weights from the first matching moments when the nodes are distinct, and exact Hankel rank when the section is large enough and every weight is nonzero.

The declaration formalizes the exact noiseless finite layer shared by Prony reconstruction, matrix-pencil methods, finite Koopman delay models, and Hankel dynamic mode decomposition. It does not assert numerical conditioning, noisy node recovery, confluent reconstruction, or an infinite-rank operator theorem.

## References

- Truth anchor: `D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction.finite_prony_hankel_reconstruction`
- Dependency: [D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography](FiniteVandermondeTomography.md)
