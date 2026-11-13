# Compression from the original regular actions

## Abstract

The original nonassociative Hilbert-space product defines an exact compression in its regular-action norm.

Let H be any finite-dimensional complex Hilbert space with a conjugate-linear additive involution. The data consist of the original continuous complex-bilinear product mu, its strict two-sided unit e with Hilbert norm one, the reversal identity for the involution, and the Hilbert-adjoint identity adjoint(L_x)=L_(star x). Assume the bilinear norm is at most M, M is at least one, and the original Hilbert associator norm is at most delta times the three input norms, with delta nonnegative.

Define p(x) as the original Hilbert operator norm of L_x. The auxiliary Banach space is the range of x mapped to L_x, with the inherited operator norm. Evaluation at e proves injectivity and identifies H linearly and continuously with this range. Actual left and right multiplication are transported through this identification. For P and Q, set T=L_P R_Q+R_Q L_P-identity and let C(P,Q) be the transport to H of one half of the sum of identity and T times the Taylor inverse-square-root series evaluated at T squared minus identity. No associative multiplication or C*-algebra instance is added to H, and the Hilbert structure on H is retained.

**Theorem 1.1 (Exact idempotence from the actual product defects).**

$$\forall P,Q\in H, \forall \tau \in \mathbb{R}, P^{*}=P, Q^{*}=Q, 0\le \tau, \tau+M \delta \le \frac{1}{1024}, \operatorname{p}\left(\operatorname{mu}\left(P, P\right)-P\right)\le \tau, \operatorname{p}\left(\operatorname{mu}\left(Q, Q\right)-Q\right)\le \tau \implies \operatorname{C}\left(P, Q\right)^{2}=\operatorname{C}\left(P, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For self-adjoint P and Q with p(mu(P,P)-P) and p(mu(Q,Q)-Q) at most tau, assume tau is nonnegative and tau+M delta is at most 1/1024. The norm of the square of T=L_P R_Q+R_Q L_P-identity minus identity is at most 512(tau+M delta) in the auxiliary operator algebra. Thus the inverse-square-root Taylor series converges. One half of the sum of identity and T times that series is exactly idempotent, and conjugation by the regular-range equivalence gives an exactly idempotent continuous linear map on the original H.

The approximate-projection bounds, left/right square defects and commutator defect are derived from mu. The mixed corner is defined as the range of this corrected map. The construction follows Kitaev, Almost-idempotent quantum channels and approximate C*-algebras, arXiv:2405.02434v2, sections 3 and 7. It is a prerequisite for the full-corner construction of Lemma 9.4; it does not establish corner saturation, an exact matrix action, compatible columns, or the block extension.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Approximate/RegularCompression.compression_idempotent`
- Dependency: [D5/S3/Quantum/Algebra/Approximate/Compression](Compression.md)
