# Local Riccati Signs from the Analytic Quotient

## Abstract

Analytic finite jets supply local signs for the actual Renyi Riccati quotient.

**Theorem 1.1 (Initial signs of the actual first and second derivatives).**

$$\forall n: \mathbb{R}, 0 < n \land n \le \frac{1}{4} \implies \exists delta, 0 < delta \land \forall z, z \in \operatorname{Ioo}\left(0, delta\right) \implies \operatorname{deriv}\left(\operatorname{C}\left(n\right), z\right) < -n \land \operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{C}\left(n\right)\right), z\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexLocal.C_local_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analytic quotient Q agrees with C(t^2) for 0<t<1. Its first and third derivatives vanish at zero, while Q''(0)=2(n^2-1)/3 and Q''''(0)=-8(1-n^2)(4-n^2)/15. The bound (n^2+3n-1)/3 <= -1/16 yields Q''(0)<-2n. CachinConvexLimits applies with slope threshold -n, and neighborhood equalities transport both square-root derivative expressions to the actual C. Thus D'=C'+n is negative near zero and C'' is negative there. No derivative of C at zero or asymptotic expansion is assumed.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexLocal.C_local_signs`
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinConvexBranch](CachinConvexBranch.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinConvexInitial](CachinConvexInitial.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/CachinConvexLimits](CachinConvexLimits.md)
