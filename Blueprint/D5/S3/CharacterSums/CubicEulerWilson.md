# The Cubic Euler Sum and Wilson's Factorial Cube

## Abstract

The double cubic Euler sum is a central binomial coefficient; Wilson gives an explicit inverse-factorial cube in prime characteristic.

**Theorem 1.1 (Wilson gives an explicit cube).**

$$\forall F, \operatorname{Field}\left(F\right), \forall p, \forall m: N, \operatorname{Prime}\left(p\right), \operatorname{CharP}\left(F, p\right), p=3m+1, \operatorname{Even}\left(m\right) \implies -\operatorname{cast}\left(\operatorname{choose}\left(2m, m\right), F\right)=\operatorname{pow}\left(\operatorname{inv}\left(\operatorname{cast}\left(\operatorname{factorial}\left(m\right), F\right)\right), 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/CubicEulerWilson.neg_binomial_eq_inverse_factorial_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be any field of characteristic p, where p is prime, p = 3m + 1 and m is even. The negative central binomial coefficient choose(2m,m), cast into F, is the cube of the inverse of m!. The proof first works in ZMod p. The descending factorial from p-1 has value m! because m is even. Wilson's theorem therefore gives (2m)! m! = -1. The binomial factorial identity and the nonvanishing of m! then give -choose(2m,m)(m!)^3 = 1. Cancellation produces the displayed cube. The canonical prime-field homomorphism transports the identity to F, with no chosen field equivalence.

This is a project derivation from the classical Wilson theorem and the factorial identities, with no novelty claim. The prime p determines the characteristic, rather than the cardinality of F. The theorem can therefore be used in extensions of the prime field, while the specific factorial index remains m = (p-1)/3.

**Theorem 1.2 (Only one exponent survives the finite-field sum).**

$$\forall F, \operatorname{FiniteField}\left(F\right), \forall m: N, \operatorname{card}\left(F\right)=3m+1, \operatorname{Even}\left(m\right) \implies \sum_{x\in F} \operatorname{pow}\left(x, 2m\right) \operatorname{pow}\left(1-x, 2m\right)=-\operatorname{cast}\left(\operatorname{choose}\left(2m, m\right), F\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/CubicEulerWilson.sum_double_cubic_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a finite field with card(F) = 3m + 1 and m even. Expand (1-x)^(2m) and sum over F. The exponents 2m+i range from 2m to 4m, so the only multiple of card(F)-1 = 3m is 3m, at i=m. The positive-exponent field power sum is -1 at that exponent and zero at the other exponents. The surviving sign (-1)^m equals one. Thus the sum is -choose(2m,m). The proof reuses Mathlib's unit-group power-sum formula and accounts for the zero field element explicitly.

This coefficient extraction is derived here from the finite-field power-sum theorem; no literature novelty is asserted. It applies to finite fields of arbitrary prime-power degree subject to the explicit even-index premise, which forces odd cardinality. Combining it with the Wilson cube requires the separate equality card(F)=p. Without that extra hypothesis, the cardinality index in this theorem and the characteristic index in the preceding theorem can differ. For the cubic reciprocity continuation this supplies the double-exponent Euler reduction of the conjugate Jacobi sum in the original residue field. It proves the finite-field evaluation only; the character-conjugation and primary-generator bridges are supplied separately.

## References

- Truth anchor: `D5/S3/CharacterSums/CubicEulerWilson.neg_binomial_eq_inverse_factorial_cube`
- Truth anchor: `D5/S3/CharacterSums/CubicEulerWilson.sum_double_cubic_euler`
- Dependency: [D5/S3/Arith/Wilson](../Arith/Wilson.md)
