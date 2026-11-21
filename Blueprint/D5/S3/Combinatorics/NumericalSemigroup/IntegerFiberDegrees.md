# Eventual degrees of nonnegative integer fibers

## Abstract

The signed degree order and a sufficient cutoff for nonnegative integer fibers.

**Theorem 1.1 (A positive solution gives consecutive degrees and a sufficient cutoff).**

$$0 < h \land (\forall N \in D, h \mid N) \land \exists b, B = hb \land (\exists u, A(u) = hw) \land (\forall u, A(u) = hw \Rightarrow \forall r, r = b(1 + \sum_{j} \Vert u_{j}\Vert) \Rightarrow 0 < r \land hr \in D \land h(r+1) \in D \land (\forall t \geq (b-1)r, ht \in D))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees.eventual_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a finite index type and I any index type. Let A be an additive homomorphism from integer-valued functions on J to integer-valued functions on I, and let w be an integer-valued function on I. Assume there is a strictly positive integer vector p on J and a positive natural number B with A(p) = B w.

Let D consist of the natural numbers N such that A(v) = N w for some nonnegative integer vector v on J. Let h be the additive order of the class of w in the quotient by the range of A.

The positive solution proves that h is finite. By the quotient equation there is an integer vector u of degree h. Adding enough copies of p to u makes every coordinate nonnegative. This gives two solutions whose degrees differ by h. For any signed solution u at degree h, multiply one plus the sum of the absolute coordinates of u by b to get r, with b = B / h. The original positive solution has normalized degree b. Since b and r + 1 are coprime, the bound for two coprime generators gives the cutoff (b − 1) r.

The finite coordinate set makes a single shift sufficient. Strict positivity lets that shift repair a negative entry at any coordinate. For example, with A(x, y, z) = (2x + y, y + z) and w = (1, 0), the nonnegative vector (1, 0, 0) has degree 2 and the signed vector (0, 1, −1) has degree 1. Every nonnegative vector on the ray has even degree. This example is verified by the two displayed equations.

The condition B > 0 supplies a positive annihilator of the quotient class. With A = 0 and a singleton target coordinate w = 1, B = 0 gives no finite order for that class.

## References

- Truth anchor: `D5/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees.eventual_counts`
