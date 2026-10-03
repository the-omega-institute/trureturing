# Trace and Norm Denominators on a Weierstrass Curve

## Abstract

Smoothness prevents a common trace and norm denominator from hiding a pole in either polynomial coordinate.

**Theorem 1.1 (A smooth coordinate ring has no hidden polynomial denominator).**

$$\forall F, \operatorname{Field}\left(F\right) \Rightarrow \forall W \in \operatorname{Weierstrass}\left(F\right), \operatorname{Smooth}\left(W\right) \Rightarrow \forall d, p, q \in \operatorname{Polynomial}\left(F\right), (d \neq 0 \land d divides \operatorname{traceNumerator}\left(W, p, q\right) \land d^{2} divides \operatorname{normNumerator}\left(W, p, q\right)) \Rightarrow (d divides p \land d divides q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/EllipticTraceNormDivisibility.elliptic_trace_norm_denominator_divides_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be any field, and let W be a smooth Weierstrass curve over F. Set A(X) = a1 X + a3 and B(X) = X cubed + a2 X squared + a4 X + a6. Its quadratic coordinate relation is Y squared + A(X) Y - B(X) = 0. For p and q in F[X], the trace numerator of p + qY is 2p - qA and the norm numerator is p squared - pqA - q squared B.

For every nonzero polynomial d, if d divides the trace numerator and d squared divides the norm numerator, then d divides both p and q. The theorem includes fields of characteristic two and three.

At a prime polynomial where q is invertible, the trace and norm relations would construct a point with both partial derivatives zero over the residue field. Smoothness rules out this singular point. Thus the prime divides both coordinates; cancelling it and applying factorization induction accounts for every denominator multiplicity.

This criterion is a step in coordinate integrality. It alone gives no global isogeny point map, point independence, or canonical height.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/EllipticTraceNormDivisibility.elliptic_trace_norm_denominator_divides_coordinates`
