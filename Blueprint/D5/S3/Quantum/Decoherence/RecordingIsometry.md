# Recording Isometry

## Abstract

The canonical projective recording map is isometric and exposes every state block.

**Theorem 1.1 (Projective recording is isometric with explicit state blocks).**

$$\forall S \in Type, A \in Type,\; \left(\operatorname{Fintype}\left(S\right) \land \left(\operatorname{DecidableEq}\left(S\right) \land \left(\operatorname{Fintype}\left(A\right) \land \operatorname{DecidableEq}\left(A\right)\right)\right)\right) \Rightarrow \left(\forall P \in A \to \operatorname{Matrix}\left(S, S, \mathbb{C}\right),\; \left(\left(\forall a \in A,\; P\left(a\right)^{*} = P\left(a\right)\right) \land \left(\left(\forall a \in A, b \in A,\; P\left(a\right) \cdot P\left(b\right) = \operatorname{ite}\left(a = b, P\left(a\right), 0\right)\right) \land \sum_{a \in A} P\left(a\right) = I\right)\right) \Rightarrow \operatorname{let} V: \operatorname{Matrix}\left(S \times A, S, \mathbb{C}\right), \forall i: S, a: A, j: S, \operatorname{entry}\left(V, \operatorname{pair}\left(i, a\right), j\right) = \operatorname{entry}\left(P\left(a\right), i, j\right); V^{*} \cdot V = I \land \left(\forall rho \in \operatorname{Matrix}\left(S, S, \mathbb{C}\right), a \in A, b \in A, i \in S, j \in S,\; \operatorname{entry}\left(V \cdot \rho \cdot V^{*}, \operatorname{pair}\left(i, a\right), \operatorname{pair}\left(j, b\right)\right) = \operatorname{entry}\left(P\left(a\right) \cdot \rho \cdot P\left(b\right), i, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/RecordingIsometry.recording_isometry_and_state_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite system and outcome carriers have decidable equality. The supplied matrices are self-adjoint orthogonal projectors whose sum is the identity.

The recording matrix is defined on the product basis by V((i,a),j) = P(a)(i,j). Its adjoint product is the identity, and conjugating any complex system matrix yields the displayed P(a) rho P(b) block.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/RecordingIsometry.recording_isometry_and_state_blocks`
