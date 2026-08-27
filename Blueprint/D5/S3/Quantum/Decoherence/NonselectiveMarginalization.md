# Nonselective Marginalization

## Abstract

The canonical finite recording map has a non-selective marginal equal to the sum of diagonal projective blocks.

**Theorem 1.1 (Tracing out the recording register gives the unread update).**

$$\forall S, A: \operatorname{Type}, \operatorname{Fintype}\left(S\right) \land \operatorname{DecidableEq}\left(S\right) \land \operatorname{Fintype}\left(A\right) \land \operatorname{DecidableEq}\left(A\right) \land P: A \to \operatorname{Matrix}\left(S, S, \mathbb{C}\right), \forall a \in A,\; \operatorname{adjoint}(P(a)) = P(a) \land \forall a \in A, b \in A,\; P(a) \cdot P(b) = \operatorname{ite}\left(a = b, P(a), 0\right) \land \sum_{a \in A} P(a) = I \Rightarrow \operatorname{let} V: \operatorname{Matrix}\left(S \times A, S, \mathbb{C}\right), \forall i, a, j: S, \operatorname{entry}\left(V, \operatorname{pair}\left(i, a\right), j\right) = \operatorname{entry}\left(P(a), i, j\right); \operatorname{let} Tr: \operatorname{Matrix}\left(S \times A, S \times A, \mathbb{C}\right) \to \operatorname{Matrix}\left(S, S, \mathbb{C}\right), \forall X, i, j: S, \operatorname{entry}\left(Tr(X), i, j\right) = \sum_{a \in A} \operatorname{entry}\left(X, \operatorname{pair}\left(i, a\right), \operatorname{pair}\left(j, a\right)\right); Tr(V rho V^{*}) = \sum_{a \in A} P(a)(rho)(P(a)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/NonselectiveMarginalization.nonselective_recording_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The system and outcome carriers are finite with decidable equality. Self-adjoint orthogonal projectors summing to the identity define the canonical recording matrix V((i,a),j) = P(a)(i,j).

The displayed partial-trace map sums equal outcome indices in each system matrix entry. Applied to V rho V^*, it therefore returns exactly the sum of the diagonal blocks P(a) rho P(a), for every complex system matrix rho.

The proof applies the frozen recording-isometry state-block theorem directly; no alternate recording or partial-trace primitive is introduced.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/NonselectiveMarginalization.nonselective_recording_marginal`
- Dependency: [D5/S3/Quantum/Decoherence/RecordingIsometry](RecordingIsometry.md)
