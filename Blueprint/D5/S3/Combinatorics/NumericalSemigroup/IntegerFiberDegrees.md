# Eventual degrees of nonnegative integer fibers

## Abstract

The signed degree order and a sufficient cutoff for nonnegative integer fibers.

**Theorem 1.1 (A positive solution gives two consecutive multiples of the quotient order).**

$$0 < h \land (\forall N \in D, h \mid N) \land \exists r, 0 < r \land hr \in D \land h(r+1) \in D \land (\forall t \geq r(r-1), ht \in D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees.eventual_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a finite index type and I any index type. Let A be an additive homomorphism from integer-valued functions on J to integer-valued functions on I, and let w be an integer-valued function on I. Assume there is a strictly positive integer vector p on J and a positive natural number B with A(p) = B w.

Let D consist of the natural numbers N such that A(v) = N w for some nonnegative integer vector v on J. Let h be the additive order of the class of w in the quotient by the range of A.

The positive solution proves that h is finite. By the quotient equation there is an integer vector u of degree h. Adding enough copies of p to u makes every coordinate nonnegative. This gives two solutions whose degrees differ by h. After dividing by h, these degrees are consecutive. The bound for nonnegative combinations of two coprime integers gives the stated cutoff.

## References

- Truth anchor: `D5/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees.eventual_counts`
