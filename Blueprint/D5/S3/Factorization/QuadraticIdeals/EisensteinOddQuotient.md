# Scalar Quotients of Oriented Eisenstein Factors

## Abstract

An odd-parameter Eisenstein factor has a scalar contraction equal to its norm ideal and a scalar quotient isomorphism.

**Theorem 1.1 (The oriented factor contracts to its norm ideal).**

$$\forall b: OddNatural, (\forall n: Z, \operatorname{Dvd}\left(\operatorname{orientedFactor}\left(b\right), \operatorname{C}\left(n\right)\right) \iff \operatorname{Dvd}\left(\operatorname{blockNorm}\left(b\right), n\right)) \land\\{}(\exists e: \operatorname{RingEquiv}\left(\operatorname{ZMod}\left(\operatorname{blockNorm}\left(b\right)\right), \operatorname{OrientedQuotient}\left(b\right)\right), \forall n: Z, \operatorname{e}\left(\operatorname{IntClass}\left(n\right)\right) = \operatorname{scalarMap}\left(b, n\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient.eisenstein_odd_scalar_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be the quadratic algebra Z[omega] with omega squared plus omega plus one equal to zero. For an odd natural number b, set eta equal to -2 + b omega and B equal to b squared plus 2b plus 4.

If eta times (u + v omega) is scalar, its omega coefficient gives bu = (b + 2)v. Oddness makes b and b + 2 coprime, so u = (b + 2)t and v = bt. The scalar product is then -Bt. Conversely, an explicit multiple of eta has scalar value B, giving the exact contraction.

The scalar map to E modulo eta has kernel BZ. Also b and B are coprime: B is congruent to four modulo b and b is odd. In the quotient, b omega = 2 and B = 0. Bezout coefficients therefore express omega as a scalar class. Every quotient class has a representative u + v omega, so the scalar map is surjective and induces the displayed ring equivalence with the stated action on integers.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient.eisenstein_odd_scalar_quotient`
