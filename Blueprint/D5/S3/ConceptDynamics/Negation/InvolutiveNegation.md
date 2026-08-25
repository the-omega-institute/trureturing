# Involutive Negation

## Abstract

Point negation selects from complements; involution adds reversible coherence.

**Theorem 1.1 (Avoidance selectors choose from point complements).**

$$\forall selector: \operatorname{AvoidanceSelector}\left(X\right), \forall x: X, \operatorname{member}\left(\operatorname{choose}\left(selector, x\right), \operatorname{pointComplement}\left(x\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/InvolutiveNegation.avoidanceSelector_mem_pointComplement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An avoidance selector carries a chosen point for every input together with the proof that the chosen point differs from that input.

Since the point complement is exactly the set of unequal points, the selector's avoidance field is precisely the required membership witness.

**Theorem 1.2 (Involutive negation induces an involutive set action).**

$$\forall negation: \operatorname{InvolutiveNegation}\left(X\right), \operatorname{imageSet}\left(negation, \operatorname{imageSet}\left(negation, A\right)\right) = A.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Negation/InvolutiveNegation.imageSet_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The subset action sends a set through the point-negation map. Membership in the image can be tested by negating the candidate point once.

Applying the image action twice negates every point twice. The structure field asserting pointwise involution then returns exactly the original subset.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Negation/InvolutiveNegation.avoidanceSelector_mem_pointComplement`
- Truth anchor: `D5/S3/ConceptDynamics/Negation/InvolutiveNegation.imageSet_involutive`
- Dependency: [D5/S3/ConceptDynamics/Negation/RelativeComplement](RelativeComplement.md)
