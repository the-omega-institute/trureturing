# Descent of Algebraic Primitives

## Abstract

An algebraic primitive of an element of a characteristic-zero differential field can be replaced by a primitive in that field.

**Theorem 1.1 (A primitive in the base field).**

Lean statement: `D5/S1/Recurrence/Algebraic/AlgebraicPrimitiveDescent.exists_primitive_of_isAlgebraic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/AlgebraicPrimitiveDescent.exists_primitive_of_isAlgebraic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a differential field of characteristic zero and let L be a nonzero commutative differential K-algebra whose derivative extends that of K. For x in L and g in K, suppose x is algebraic over K and x' is the image of g. Then there is h in K with h'=g. To see this, write the monic minimal polynomial of x as P(Y)=Y^n+aY^(n-1)+lower terms, with n positive. Differentiating P(x)=0 gives a second polynomial relation Q(x)=0, where Q is the coefficient derivative of P plus g times its formal polynomial derivative. The leading coefficient of P is one, so Q has degree less than n; minimality forces Q to vanish identically. Its coefficient of Y^(n-1) is a'+ng, and therefore h=-a/n is the required primitive. This proof is repository-derived and uses the coefficient-wise derivation and minimal-polynomial results from Mathlib.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/AlgebraicPrimitiveDescent.exists_primitive_of_isAlgebraic`
