# Periodicity Tests for Two-Sided Payoff Shifts

## Abstract

Bounded irrational discrepancy excludes repetition, and finite two-sided edge presentations yield periodic points.

**Theorem 1.1 (Bounded discrepancy excludes a positive period).**

$$\forall (a: \mathbb{Z} \to Bool), \forall (\alpha: \mathbb{R}), (Irrational\left(\alpha\right)) \Rightarrow ((\forall (i: \mathbb{Z}), \forall (n: \mathbb{N}), (2 \le n) \Rightarrow (\left|D\left(a, \alpha, i, n\right)\right| \le 7)) \Rightarrow (\neg (\exists (p: \mathbb{Z}), 0 < p \land Periodic\left(a, p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity.no_positive_period_of_irrational_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here D(a, α, i, n) is the number of true letters of a at coordinates i through i + n − 1 minus nα. For a positive period p containing c true letters, a window of k periods has discrepancy k(c − pα). Irrationality makes its absolute value exceed seven for large enough k.

**Theorem 1.2 (A nonempty finite edge presentation yields a periodic point).**

$$\forall (V: Type), \forall (E: Type), \forall (A: Type), [Finite\left(V\right)] [Finite\left(E\right)], \forall (s: E \to V), \forall (t: E \to V), \forall (l: E \to A), \forall (Y: Set\left((\mathbb{Z} \to A)\right)), (Presented\left(s, t, l, Y\right)) \Rightarrow ((Nonempty\left(Y\right)) \Rightarrow (\exists (x: \mathbb{Z} \to A), x \in Y \land \exists (p: \mathbb{Z}), 0 < p \land Periodic\left(x, p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity.exists_periodic_point_of_finite_edge_presentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite vertex and edge types and the alphabet can lie in arbitrary universes. Presented means that for every integer-indexed alphabet point, membership is equivalent to the existence of an integer-indexed edge walk whose target at each index is the source at its successor and whose label is the point at that index. A repeated vertex on the nonnegative ray gives a positive-length closed edge walk. Remainders modulo its length extend that walk over all integers, including its seam.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity.exists_periodic_point_of_finite_edge_presentation`
- Truth anchor: `D5/S1/Dynamics/Symbolic/BiInfinitePayoffPeriodicity.no_positive_period_of_irrational_discrepancy`
