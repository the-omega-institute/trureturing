# Finite Integral Column Normalization

## Abstract

Finite Bezout elimination of integral sampling columns.

**Theorem 1.1 (Finite column gcd normalization).**

$$\forall I: TypeStar, \operatorname{DecidableEq}\left(I\right), \forall s: \operatorname{Finset}\left(I\right), \forall p: I, \forall a: \mathbb{Z}, \forall v: I \to \mathbb{Z}, (\neg \operatorname{mem}\left(p, s\right)) \Rightarrow (\exists e: \operatorname{LinearEquiv}\left(\mathbb{Z}, I \to \mathbb{Z}, I \to \mathbb{Z}\right), \forall x: I \to \mathbb{Z}, ((x(p) = a) \land (\forall i: I, (\operatorname{mem}\left(i, s\right)) \Rightarrow (x(i) = v(i)))) \Rightarrow (\forall i: I, e(x)(i) = \operatorname{if}\left(i = p, \operatorname{IntCast}\left(\operatorname{gcd}\left(\Vert a \Vert, \operatorname{gcdFinite}\left(s, fun j \Rightarrow \Vert v(j) \Vert\right)\right)\right), \operatorname{if}\left(\operatorname{mem}\left(i, s\right), 0, x(i)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FiniteColumnGcdNormalization.finite_column_gcd_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any coordinate type with decidable equality, a finite set s, a pivot p outside s, an integer a and an integer column v, an integer linear automorphism e satisfies the displayed formula for every x with x(p)=a and x(i)=v(i) on s. Negative inputs and a zero gcd are included. Finite-set induction combines the current pivot and each new coordinate by an invertible two-coordinate Bezout transformation. This supplies the integral column reduction needed after clearing the first row of a finite Fibonacci sampling matrix.

## References

- Truth anchor: `D5/S1/Recurrence/FiniteColumnGcdNormalization.finite_column_gcd_normalization`
