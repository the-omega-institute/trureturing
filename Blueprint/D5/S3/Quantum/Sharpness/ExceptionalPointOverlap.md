# Exceptional-Point Branch Overlap

## Abstract

The normalized overlap of the two explicit PT branches is the smaller coupling ratio.

**Theorem 1.1 (The PT branch overlap is the smaller coupling ratio).**

$$\forall delta,kappa \in \mathbb{R},\ 0<delta \land 0<kappa \Rightarrow \operatorname{overlap}(delta,kappa) = \operatorname{min}(\frac{delta}{kappa}, \frac{kappa}{delta})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/ExceptionalPointOverlap.exceptional_point_branch_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real parameters delta and kappa, the formal module writes the two branch vectors explicitly. Before the exceptional point their second coordinates use the real radical sqrt(kappa^2 - delta^2); after it they use i times delta plus or minus sqrt(delta^2 - kappa^2). The overlap is the absolute Hermitian inner product divided by the product of the Euclidean norms.

The proof splits at delta <= kappa. In the first phase both squared norms are 2 kappa^2 and the inner-product norm is 2 delta kappa, giving delta/kappa. In the second phase the norm product is 2 delta kappa and the inner-product norm is 2 kappa^2, giving kappa/delta. Positivity then identifies the applicable ratio with their minimum.

This node closes only the explicit two-by-two branch-overlap formula in the source theorem. It does not formalize the attached zeta, PT, RH, Lehmer-pair, exceptional-point-sensing, or double-clock interpretations.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/ExceptionalPointOverlap.exceptional_point_branch_overlap`
