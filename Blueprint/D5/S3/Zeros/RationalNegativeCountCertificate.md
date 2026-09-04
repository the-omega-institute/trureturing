# Rational Negative-Count Certificate

## Abstract

A nonempty open negative-count region contains a rational parameter certificate.

**Theorem 1.1 (Failure in an open negative-count region has rational parameters).**

$$\forall RH \in \operatorname{Prop}\left(\right), Q \in \operatorname{Real}\left(\right) \to \left(\operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right)\right),\; \left(\operatorname{IsOpen}\left(\operatorname{negativeCountRegion}\left(Q\right)\right) \land \left(\left(\neg RH\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{negativeCountRegion}\left(Q\right)\right)\right)\right) \Rightarrow \left(\left(\neg RH\right) \Rightarrow \left(\exists q \in \operatorname{Rat}\left(\right), r \in \operatorname{Rat}\left(\right),\; 0 < r \land \left(0 < \operatorname{apply}\left(Q, q, r\right) \land \operatorname{radialLogDerivative}\left(Q, q, r\right) < 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/RationalNegativeCountCertificate.rational_negative_count_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q(q,r) be a real two-parameter counting profile. Define the negative-count region by r > 0, Q(q,r) > 0, and a negative scale-weighted radial derivative r times d/dr log Q(q,r). If this region is open and failure of RH makes it nonempty, then it contains a point with both q and r rational.

The proof applies the dense rational embedding in each real coordinate, uses Mathlib's product theorem for dense ranges, and extracts a preimage in the supplied open region. Membership gives all three displayed certificate inequalities at once.

The source invokes a negative open set but does not state the analytic hypotheses that establish openness or produce a real witness from failure of RH. The formal theorem exposes those two bridge facts as premises. Positivity of Q at the witness makes the real logarithm semantically nondegenerate, and strict negativity excludes the zero value returned by Lean's total derivative at a nondifferentiability point.

## References

- Truth anchor: `D5/S3/Zeros/RationalNegativeCountCertificate.rational_negative_count_certificate`
