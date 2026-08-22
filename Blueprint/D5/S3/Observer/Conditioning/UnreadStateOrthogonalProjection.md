# Unread-State Orthogonal Projection

## Abstract

Unread measurement projects orthogonally onto block-diagonal matrices.

**Theorem 1.1 (Unread measurement is the block-diagonal orthogonal projection).**

$$\begin{gathered}\forall n, \kappa, P: \kappa \to M_{n}(\mathbb{C}), \operatorname{Finite}\left(n\right), \operatorname{Finite}\left(\kappa\right),\\{}\operatorname{CompleteOrthogonalProjectionFamily}\left(P\right), (\forall X\in M_{n}(\mathbb{C}), \mathcal{D}_{P}(X) = \sum_{i} P_{i} X P_{i}),\\{}\mathcal{B}_{P} = \{X \mid \forall i, j, i \neq j \Rightarrow P_{i} X P_{j} = 0\},\\{}\Rightarrow\\{}(\forall X, \mathcal{D}_{P}(\mathcal{D}_{P}(X)) = \mathcal{D}_{P}(X)) \land\\{}(\forall X, Y, \langle \mathcal{D}_{P}(X), Y\rangle_{HS} = \langle X, \mathcal{D}_{P}(Y)\rangle_{HS}) \land\\{}\operatorname{range}\left(\mathcal{D}_{P}\right) = \mathcal{B}_{P} \land\\{}(\forall X, X = \mathcal{D}_{P}(X) + (X - \mathcal{D}_{P}(X)) \land \langle \mathcal{D}_{P}(X), X - \mathcal{D}_{P}(X)\rangle_{HS} = 0) \land\\{}(\forall X, \left\lVert X \right\rVert_{HS}^{2} = \left\lVert \mathcal{D}_{P}(X) \right\rVert_{HS}^{2} + \left\lVert X - \mathcal{D}_{P}(X) \right\rVert_{HS}^{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection.unread_state_orthogonal_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a finite complete family of pairwise orthogonal self-adjoint idempotent complex matrix projections. The unread measurement channel is constructed as the sum of the compressed blocks P_i X P_i; it is not defined from the target range.

The channel is idempotent and self-adjoint for the trace pairing. Its range is exactly the matrices whose P_i X P_j cross blocks vanish when i and j differ.

Every matrix splits into its unread image and discarded residual. These two named components are Hilbert--Schmidt orthogonal, and the existing trace definition of squared Hilbert--Schmidt norm gives the displayed Pythagorean identity.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection.unread_state_orthogonal_projection`
- Dependency: [D5/S3/Observer/Conditioning](../Conditioning.md)
- Dependency: [D5/S3/Quantum/Tomography/RankOneContextCommutator](../../Quantum/Tomography/RankOneContextCommutator.md)
