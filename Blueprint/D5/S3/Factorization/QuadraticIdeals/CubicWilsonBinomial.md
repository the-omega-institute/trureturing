# Conjugate Primary Symbols from Wilson's Identity

## Abstract

The Wilson binomial identity makes the conjugate primary generator a cube in the original residue field.

Fix E = Z[omega], the Eisenstein order with its standard conjugation star. For a finite maximal quotient, chi_P denotes the actual Euler cubic residue character E/P -> E, extended by zero at zero. Writing chi_P(a) for a in E means evaluation at a mod P. A primary generator pi satisfies span{pi} = P and 3 divides pi-1. Cardinalities are natural-number cardinalities; on finite quotients these agree with the cardinalities of the chosen finite enumerations. The finite-field identities of CubicEulerWilson and the Jacobi normalization give the following classical arithmetic consequences. These are project derivations from those identities, with no claim of literature novelty.

**Theorem 1.1 (Conjugating the Jacobi sum doubles the Euler exponents).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{mod}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right), 3\right)=1, \neg \operatorname{member}\left(\operatorname{cast}\left(3, E\right), P\right) \implies \operatorname{modIdeal}\left(\operatorname{star}\left(\operatorname{jacobiSum}\left(\operatorname{chi}\left(P\right), \operatorname{chi}\left(P\right)\right)\right), P\right)=\sum_{x\in \operatorname{quotient}\left(E, P\right)} \operatorname{pow}\left(x, 2\operatorname{natDiv}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)-1, 3\right)\right) \operatorname{pow}\left(1-x, 2\operatorname{natDiv}\left(\operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)-1, 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.cubicJacobiSum_star_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only that P is maximal, E/P is finite, its cardinality is 1 modulo 3, and 3 is not in P. Choose a finite enumeration of E/P and put m = (card(E/P)-1)/3. Conjugation of the character is its inverse, and its cube is the trivial multiplicative character, so the inverse is its square. Conjugation commutes with the Jacobi sum, and reduction of the squared character gives x^(2m). This reduction includes x=0: the actual character is extended by zero there. Applying the same identity at 1-x gives the displayed sum, entirely in E/P. No prime-cardinality hypothesis or identification with a conjugate quotient is used in this theorem.

**Theorem 1.2 (The conjugate generator reduces to an explicit factorial cube).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \forall p: Nat, \operatorname{prime}\left(p\right), \operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)=p, \operatorname{mod}\left(p, 3\right)=1, \forall pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(\operatorname{cast}\left(3, E\right), pi-1\right) \implies \operatorname{modIdeal}\left(\operatorname{star}\left(pi\right), P\right)=\operatorname{pow}\left(\operatorname{neg}\left(\operatorname{inv}\left(\operatorname{cast}\left(\operatorname{factorial}\left(\operatorname{natDiv}\left(p-1, 3\right)\right), \operatorname{quotient}\left(E, P\right)\right)\right)\right), 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.primary_conjugate_reduction_eq_factorial_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypotheses are exactly: P is maximal, E/P is finite of cardinality the rational prime p, p is congruent to 1 modulo 3, and pi is a specified primary generator of P. Put m = (p-1)/3. The existing normalization gives pi = -J(chi_P,chi_P). In this same quotient E/P, conjugating J replaces each character by its inverse, which is its square. Euler reduction therefore gives the sum of x^(2m)(1-x)^(2m). Only exponent 3m = p-1 survives its binomial expansion; m is even, so the value is -binomial(2m,m). The imported Wilson identity makes that value (m!^(-1))^3. The minus sign in pi = -J yields the displayed cube (-m!^(-1))^3. No isomorphism between conjugate residue fields, and no transport of their characters, occurs. Prime cardinality p is an explicit premise here; characteristic p alone is insufficient to apply this endpoint.

**Theorem 1.3 (The conjugate-primary symbol equals one).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \forall p: Nat, \operatorname{prime}\left(p\right), \operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)=p, \operatorname{mod}\left(p, 3\right)=1, \forall pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(\operatorname{cast}\left(3, E\right), pi-1\right) \implies \operatorname{chi}\left(P, \operatorname{modIdeal}\left(\operatorname{star}\left(pi\right), P\right)\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.cubic_character_conjugate_primary_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same prime-cardinality and primary-generator hypotheses, put m = (p-1)/3. Because m < p, the factorial m! is nonzero in characteristic p. Thus y = -(m!)^(-1) is nonzero, and the preceding identity gives star(pi) mod P = y^3. Fermat's theorem gives y^(p-1)=1, hence (star(pi) mod P)^m=1. Euler reduction of the actual character has this value. The character value is one of the three cubic roots in E, and reduction is injective on these roots since 3 is not in P. Therefore chi_P(star(pi))=1. The cube witness, its nonvanishing, the Jacobi value and the symbol equality are derived from the stated hypotheses.

**Theorem 1.4 (Both conjugate-primary symbols equal one).**

$$\forall P,Q: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{maximal}\left(Q\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, Q\right)\right), \forall p: Nat, \operatorname{prime}\left(p\right), \operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)=p, \operatorname{card}\left(\operatorname{quotient}\left(E, Q\right)\right)=p, \operatorname{mod}\left(p, 3\right)=1, \forall pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(\operatorname{cast}\left(3, E\right), pi-1\right), \operatorname{spanSingleton}\left(\operatorname{star}\left(pi\right)\right)=Q \implies \operatorname{chi}\left(P, \operatorname{modIdeal}\left(\operatorname{star}\left(pi\right), P\right)\right)=1 \land \operatorname{chi}\left(Q, \operatorname{modIdeal}\left(pi, Q\right)\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.conjugate_primary_symbol_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Q is also maximal with finite quotient of cardinality the same prime p, and Q = span{star(pi)}. These cardinalities are both hypotheses; their equality is not obtained from an unstated quotient identification. Since m < p, the factorial in the cube witness is nonzero. Fermat's theorem and Euler reduction give chi_P(star(pi)) = 1 after using injectivity on the three actual cubic roots. Conjugation preserves the primary congruence, so applying this same theorem independently in E/Q gives chi_Q(pi) = 1. Neither a cube witness, nonvanishing of the input, a Jacobi value, nor a symbol equality is supplied as an endpoint hypothesis. This statement assumes both prime-cardinality equalities; it does not derive them from characteristic data.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.conjugate_primary_symbol_pair`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.cubicJacobiSum_star_reduction`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.cubic_character_conjugate_primary_eq_one`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.primary_conjugate_reduction_eq_factorial_cube`
- Dependency: [D5/S3/CharacterSums/CubicEulerWilson](../../CharacterSums/CubicEulerWilson.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius](CubicGaussFrobenius.md)
