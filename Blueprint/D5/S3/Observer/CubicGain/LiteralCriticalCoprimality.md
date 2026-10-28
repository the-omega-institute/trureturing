# The full FC coefficient list

## Abstract

Coprimality of the literal critical polynomial and its derivative

F is exactly criticalPolynomial from ExactW3Center: the sixty-eight descending integer coefficients FC of VI, Lemma 4.2 and Section 10, interpreted as a real polynomial. No root, interval or specialized source parameter is selected.

An integer polynomial with those same coefficients reduces modulo 101 to a degree-67 polynomial whose derivative has degree 66. Explicit integer polynomials satisfy U F + V F'=1+101 W. Reduction gives a full Bezout identity over ZMod 101, which proves that the modular resultant is nonzero. Compatibility of the fixed-degree resultant with coefficient homomorphisms then proves that the integer and rational resultants are nonzero. The resultant criterion gives coprimality over the rationals, and coefficient extension gives the stated real-polynomial conclusion.

**Theorem 1.1 (The original FC has no repeated algebraic factor).**

$$\operatorname{IsCoprime}(\operatorname{criticalPolynomial}(), \operatorname{derivative}(\operatorname{criticalPolynomial}()))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralCriticalCoprimality.critical_polynomial_is_coprime_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal criticalPolynomial and its formal derivative are coprime. Equivalently, their gcd is a nonzero constant. The proof first establishes this statement over Q and then over R; it requires no assumption about any particular root.

**Theorem 1.2 (The literal FC is primitive with positive leading coefficient).**

$$\exists f\in \operatorname{Polynomial}(\mathbb{Z}), \operatorname{realMap}(f)= \operatorname{criticalPolynomial}()\land \operatorname{natDegree}(f)= 67\land \operatorname{IsPrimitive}(f)\land 0< \operatorname{leadingCoeff}(f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/LiteralCriticalCoprimality.literal_critical_integer_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same sixty-eight integer coefficients define a primitive degree-67 integer polynomial with positive leading coefficient whose real image is exactly criticalPolynomial. In the formula, realMap is coefficient extension along Int.castRingHom R. Primitivity follows because its coefficients of degrees 59 and 67 are coprime integers.

These results prove the literal FC normalization and F,F' coprimality clauses. The original fixed determinant identities, both primitive gcd factorizations, the identification of h and the reduced a,c, their other coprimalities, and the complete root, lift and world exhaustion remain separate obligations.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/LiteralCriticalCoprimality.critical_polynomial_is_coprime_derivative`
- Truth anchor: `D5/S3/Observer/CubicGain/LiteralCriticalCoprimality.literal_critical_integer_normalization`
- Dependency: [D5/S3/Observer/CubicGain/ExactW3Center](ExactW3Center.md)
