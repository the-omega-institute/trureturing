# Weighted Residue-Prefix Rectangle Moments

## Abstract

Actual residue-prefix caps transfer weighted second moments of arbitrary finite layers.

**Theorem 1.1 (An explicit bound for the actual joint rectangle load).**

Lean statement: `D5/S3/Arith/Congruence/PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and I be finite types and p and H natural numbers. The old weights mu(x) and all layer coefficients A(e,i,x) are nonnegative. At each old point x, K(x,y) is a nonnegative probability distribution on Fin(p^H). For every depth t from one through H, every residue r and every x, assume the K-mass of y mod p^t = r mod p^t is at most M(t,x). This envelope may depend on both t and x.

Assume the zero layer's mu-weighted second moment is at most G(0). For every positive depth t and each exponent e at most t, assume the second moment of the layer sum over I, weighted by mu(x)M(t,x), is at most G(t). Choose arbitrary natural residues b(e,i). The new load sums A(e,i,x) over those pairs whose residue condition y mod p^e = b(e,i) mod p^e holds. Its squared expectation under mu(x)K(x,y) is at most G(0) plus the sum, for t from one through H, of (2t+1)G(t).

The proof bounds each actual intersection by its deeper cylinder, derives nonnegativity of the prefix envelope from the kernel, and controls cross-layer moments by weighted Young's inequality. Kernel normalization handles the zero-exponent pair without distortion. An induction counts exactly 2t+1 ordered exponent pairs with maximum t.

The statement includes H = 0. It needs neither primality of p, normalization of mu, independence from x, nor compatible choices of the test residues. This is the rectangle estimate used in joint-load arguments for distinct covering systems. Constructing the probability kernel and embedding a divisor layout by the Chinese remainder theorem are separate proof obligations; this theorem does not settle the odd covering problem.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le`
