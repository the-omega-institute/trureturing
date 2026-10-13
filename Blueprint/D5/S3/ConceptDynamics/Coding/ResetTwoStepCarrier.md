# Two-step reset carrier coefficients

## Abstract

The actual reset square and its identity summand retain their separate origin coefficients for every positive order.

Sign is Multiplicative Bool with the original XOR law, and SignIdentity is its identity. resetMatrix q has the reset label ofAdd true into age zero and the identity-labelled advance when the next age is less than q. twoStepMatrix q is the product resetMatrix q * resetMatrix q, and twoStepCarrier q adds the identity matrix. origin hq is age zero; NatPositive(q) means 0<q. coefficientAt(M,i,j,g) denotes the natural-number coefficient of g in M(i,j).

**Theorem 1.1 (The reset square has one identity-labelled origin path).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{coefficientAt}\left(\operatorname{twoStepMatrix}\left(q\right), \operatorname{origin}\left(hq\right), \operatorname{origin}\left(hq\right), SignIdentity\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetTwoStepCarrier.twoStep_origin_square_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the product coefficient sum, the intermediate age zero contributes the two reset edges FF. Their two flip labels multiply to the identity. Every other intermediate age contributes zero to this coefficient. The conclusion holds for all positive q, including q=1 where advances are absent.

**Theorem 1.2 (The carrier has two separately numbered origin boundaries).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{coefficientAt}\left(\operatorname{twoStepCarrier}\left(q\right), \operatorname{origin}\left(hq\right), \operatorname{origin}\left(hq\right), SignIdentity\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetTwoStepCarrier.twoStep_origin_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity summand contributes one coefficient and the reset square contributes one. Thus the empty path and FF occupy distinct coefficient numbers zero and one, even though both have the same origin endpoints and identity label. ResetTwoStepArithmetic uses this coefficient calculation in its actual numberedBoundaryEquiv for every positive q. The history automorphism in that module separately retains the hypothesis 4 divides q; the coefficient calculation imposes no such restriction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetTwoStepCarrier.twoStep_origin_coeff`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetTwoStepCarrier.twoStep_origin_square_coeff`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNumberedHistories](ResetNumberedHistories.md)
