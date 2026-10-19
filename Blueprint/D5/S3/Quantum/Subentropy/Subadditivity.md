# Subadditivity of subentropy

## Abstract

Subentropy is subadditive for every finite bipartite density state.

Datta, Dorlas, Jozsa and Benatti state: "Conjecture 1. Subentropy is subadditive: Q(ρAB) ≤ Q(ρA) + Q(ρB)." The locator is arXiv:1310.1312v1, §2.3.1, Conjecture 1.

Zhang, Singh and Pati restate the unresolved question at arXiv:1510.08859v2 §7.1: "At present, we do not know wether the subadditivity inequality of subentropy is true or not".

**Theorem 1.1 (Subentropy is subadditive).**

Lean statement: `D5/S3/Quantum/Subentropy/Subadditivity.subentropy_subadditive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/Subadditivity.subentropy_subadditive` (`✓ std3`). ∎

*Resolves.* `Problems/datta-dorlas-jozsa-benatti-2014-subentropy-subadditivity` (proved) by `D5/S3/Quantum/Subentropy/Subadditivity.subentropy_subadditive`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"datta-dorlas-jozsa-benatti-2014-subentropy-subadditivity","declaration_gid":"D5/S3/Quantum/Subentropy/Subadditivity.subentropy_subadditive","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For every pair of finite coordinate types A and B and every density state ρ on A×B, subentropy ρ ≤ subentropy (marginalRight ρ) + subentropy (marginalLeft ρ). marginalRight traces out B and retains A; marginalLeft traces out A and retains B. No rank, nonzero-probability or nondegenerate-spectrum assumption is imposed. The trace-one condition itself excludes empty state spaces.

The pinching gap is convex on density matrices. Decompose a matrix spectrally into weighted normalized pure states. For a pure state, rectangular Gram invariance identifies its pinching gap with the classical subentropy of its block norm squares. Concavity of classical subentropy then bounds the original gap by the classical subentropy of the block trace weights. This is an actual joint decomposition of one density matrix throughout.

For arbitrary positive blocks Y_x of total trace one, form the rectangular map V whose block columns are sqrt(Y_x). Then VV-adjoint=Σ_x Y_x and block pinching of V-adjoint V is the direct sum of Y_x. Rectangular Gram invariance and the pinching upper bound yield Q(directSum Y)≤Q(ΣY)+Q_cl((tr Y_x)_x). The construction includes zero blocks without normalization.

Change ρ locally into an eigenbasis of its A marginal. The positive diagonal blocks sum to its original B marginal, and their traces are exactly the A marginal's eigenvalues. Nonnegative pinching gap gives Q(ρ)≤Q(pinched ρ), the preceding classical-quantum bound gives the required upper bound, and unitary invariance identifies the classical eigenvalue subentropy with Q(ρ_A). All marginals arise from the same joint state.

The functional is the canonical determinant-integral subentropy. The StrongSubadditivityRefutation.SubentropyLike specification requires continuity on all finite density states, unitary invariance and the paper's distinct positive spectral formula. Its identification theorem subentropyLike_eq proves that every such family equals subentropy, including repeated and zero eigenvalues. Thus the canonical theorem applies to the paper's subentropy and to every family satisfying that specification.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/Subadditivity.subentropy_subadditive`
- Dependency: [D5/S3/Quantum/Subentropy/EigenbasisBlocks](EigenbasisBlocks.md)
- Dependency: [D5/S3/Quantum/Subentropy/PinchingGap](PinchingGap.md)
