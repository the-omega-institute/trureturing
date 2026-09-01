# Canonical Szego SU(1,1) Transfer Matrix

## Abstract

The normalized Szego transfer matrix has the canonical determinant and preserves the Hermitian form of signature (1,1).

**Theorem 1.1 (The canonical Szego transfer is normalized special unitary).**

$$\forall alpha \in \mathbb{C}, z \in \mathbb{C}, w \in S^{1},\; \left(\operatorname{norm}\left(alpha\right) < 1 \land w^{2} = z\right) \Rightarrow \left(0 < \operatorname{rho}\left(alpha\right) \land \left(\operatorname{det}\left(\operatorname{A}\left(alpha, z\right)\right) = z \land \operatorname{IsSpecialUnitary11}\left(\operatorname{normalizedA}\left(alpha, w\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Szego/CanonicalTransfer.canonical_szego_su11_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Verblunsky coefficient is required to lie in the open unit disk. This makes rho(alpha) positive and proves directly that the unnormalized-phase transfer has determinant z.

A point w on the unit circle with w squared equal to z records the chosen phase square root. The normalized matrix has determinant one and its conjugate transpose preserves diag(1,-1).

The module also verifies the alpha=0 diagonal case and the explicit alpha=1/2, z=2 matrix with rho=sqrt(3)/2 and determinant two. No Li-Clark uniqueness or hyperbolicity claim is asserted.

## References

- Truth anchor: `D5/S3/Weil/Szego/CanonicalTransfer.canonical_szego_su11_transfer`
