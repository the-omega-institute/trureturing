# Primitive conductors for quadratic products

## Abstract

Primitive levels and all coefficients of six quadratic characters

Let q and d be distinct odd primes. For natural n, write Jₚ(n) = (n/p) for the Jacobi symbol, and E(n) for the standard character χ₈ evaluated at n modulo eight. Products below are pointwise, with integer values cast to the complex numbers. Write R(a,f) if a primitive character of level a takes the value f(n) at every natural n.

**Theorem 1.1 (Native levels for the six quadratic coefficient functions).**

$$\left(\left(\left(\left(\operatorname{R}\left(q, Jq\right) \land \operatorname{R}\left(8 q, E Jq\right)\right) \land \operatorname{R}\left(d, Jd\right)\right) \land \operatorname{R}\left(8 d, E Jd\right)\right) \land \operatorname{R}\left(q d, Jq Jd\right)\right) \land \operatorname{R}\left(8 q d, E Jq Jd\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/PrimitiveQuadraticConductors.six_quadratic_levels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The primitive quadratic character of an odd prime gives Jₚ. At level eight, χ₈(5) = −1 rules out a lift from four, where 5 represents the identity. Multiplying characters with coprime conductors multiplies their conductors. The coefficient identity holds on units by change of level, and on nonunits because a local factor and the character on the product level both vanish.

For the next statement the coefficient values may lie in any commutative monoid with zero. Fix positive levels r and a and a positive test modulus M. Let χ be primitive of level r and suppose f has a primitive representative of level a. Write C(n) for the value of χ at n modulo r. Assume C(n) = f(n) for every n coprime to M.

**Theorem 1.2 (Agreement on integers coprime to a test modulus recovers every value).**

$$r = a \land \left(\forall n \in \mathbb{N},\; \operatorname{C}\left(n\right) = \operatorname{f}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/PrimitiveQuadraticConductors.inducing_level_and_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lift both primitive characters to level raM. Every unit there has a natural representative coprime to M, so the lifted characters agree. Taking conductors identifies r with a. Injectivity of the change of level then identifies the characters on their common native level, including their values at integers sharing factors with M.

## References

- Truth anchor: `D5/S3/CharacterSums/PrimitiveQuadraticConductors.inducing_level_and_values`
- Truth anchor: `D5/S3/CharacterSums/PrimitiveQuadraticConductors.six_quadratic_levels`
- Dependency: [D5/S3/Analytic/Zeta/MercaImaginaryCharacter](../Analytic/Zeta/MercaImaginaryCharacter.md)
