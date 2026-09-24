# The involution factorization as an exact exchange

## Abstract

An involution supplies explicit nonnegative factors and an exact one-step exchange chain with a proved lower bound.

**Theorem 1.1 (Natural coefficients satisfy both products).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), s \in H, t \in H, hs \in \operatorname{product}\left(s, s\right) = 1,\; \operatorname{product}\left(\operatorname{toNat}\left(\operatorname{leftFactor}\left(s, t\right)\right), \operatorname{toNat}\left(\operatorname{rightFactor}\left(s\right)\right)\right) = \operatorname{sourceNat}\left(s, t\right) \land \operatorname{product}\left(\operatorname{toNat}\left(\operatorname{rightFactor}\left(s\right)\right), \operatorname{toNat}\left(\operatorname{leftFactor}\left(s, t\right)\right)\right) = \operatorname{targetNat}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy.natural_factor_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative integer factors are converted coefficientwise to natural coefficients. Lifting back is injective, so the two actual products equal the original source and target formulas.

**Theorem 1.2 (Construct the one-step matrix chain).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), s \in H, t \in H, hs \in \operatorname{product}\left(s, s\right) = 1,\; \operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), \operatorname{sourceMatrix}\left(s, t\right), \operatorname{targetMatrix}\left(H\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy.involution_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-vertex matrices contain the constructed natural factors. A single rectangular exchange yields the given endpoints without a chain-existence assumption.

**Theorem 1.3 (The chain cannot have length zero).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), s \in H, t \in H, hs \in \operatorname{product}\left(s, s\right) = 1, hst \in \left(\neg \operatorname{product}\left(s, t\right) = \operatorname{product}\left(t, s\right)\right),\; \operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), \operatorname{sourceMatrix}\left(s, t\right), \operatorname{targetMatrix}\left(H\right), 1\right) \land \left(\neg \operatorname{ExchangeChain}\left(\operatorname{MonoidAlgebra}\left(Nat, H\right), \operatorname{sourceMatrix}\left(s, t\right), \operatorname{targetMatrix}\left(H\right), 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy.involution_minimum_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Noncommuting elements make the source and target coefficients different. A zero-length exchange chain has equal endpoints, while the explicit factors already give a length-one chain.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy.involution_exchange`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy.involution_minimum_one`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy.natural_factor_products`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupOverlap](CountedGroupOverlap.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange](InvolutionUniformExchange.md)
