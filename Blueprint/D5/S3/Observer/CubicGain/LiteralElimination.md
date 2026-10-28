# Literal elimination in the original coordinates

## Abstract

Literal normalized minors and fixed elimination matrices

The source circuit is sourceJ, sourceN, sourceD, sourceC and sourceNumerator of SelectedRootCommonZero. Its three numerator entries are at clocks five, six and seven. sourceBt and sourceBb are the formal partial derivative numerators in the independent t,b coordinates. sourceE0 and sourceE1 are the ordered pairs (0,1) and (0,2). sourceE2 is the explicit integral polynomial for the ordered pair (1,2), with polynomial variable r and coefficient parameter b. All signs and the scale 45 use this order.

**Theorem 1.1 (The third division-free normalization).**

$$\forall t,b\in \mathbb{R}, 45\operatorname{sourceD}(t,b)\operatorname{eval}(E_{2}(b),tb)= b^{7}(\operatorname{sourceBt}(1,t,b)\operatorname{sourceBb}(2,t,b)-\operatorname{sourceBb}(1,t,b)\operatorname{sourceBt}(2,t,b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralElimination.source_e2_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t,b, the identity identifies 45 D(t,b) E2(tb,b) with b^7 times the original ordered derivative minor M12. No nonzero condition is imposed on b, D or a leading coefficient. The identity therefore includes b=0 and every zero of D. It does not define a pointwise quotient at those zeros.

The complete elimination identities additionally require the literal Sylvester determinants, their exact factorizations, positive primitive gcd normalization and coprimality. This normalization alone gives none of those conclusions, nor any exhaustion of real roots, original worlds or lifted sources.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/LiteralElimination.source_e2_normalization`
- Dependency: [D5/S3/Observer/CubicGain/ActualMinorLift](ActualMinorLift.md)
