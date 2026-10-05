# Arithmetic of Separated Marked Prefixes

## Abstract

Arithmetic of Separated Marked Prefixes.

**Definition 1.1 (The marked powers).**

$$\forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; \operatorname{markedPowers}\left(m, p\right) = \operatorname{sum}\left(\operatorname{range}\left(m\right), s:\mathbb{N} \mapsto 2^{p + 3 \cdot s}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic.markedPowers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The marked block is the sum of positive powers at positions p, p+3, up to p+3(m-1).

**Definition 1.2 (The literal separated marked prefix).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall T \in \mathbb{Z},\; \operatorname{markedPrefix}\left(n, m, p, T\right) \Leftrightarrow \left(\operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right) = \operatorname{cast}\left(\operatorname{markedPowers}\left(m, p\right), \mathbb{Z}\right) + T \land \left(\exists tail \in \operatorname{List}\left(\mathbb{Z}\right),\; \left(\left(\operatorname{foldr}\left(\lambda z:\mathbb{Z} x:\mathbb{Z} \mapsto z + 2 \cdot x, 0, tail\right) = T \land \left(\forall z \in \mathbb{Z},\; z \in tail \Rightarrow \left(z = \operatorname{neg}\left(1\right) \lor \left(z = 0 \lor z = 1\right)\right)\right)\right) \land \operatorname{IsChain}\left(tail, \lambda a:\mathbb{Z} b:\mathbb{Z} \mapsto a = 0 \lor b = 0\right)\right) \land \left(\forall k \in \mathbb{N},\; \operatorname{getD}\left(\operatorname{getElemOption}\left(tail, k\right), 0\right) \ne 0 \Rightarrow k + 3 \le p\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic.markedPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rounded half-endpoint is the marked block plus a signed tail. The tail is a finite nonadjacent expansion with coefficients minus one, zero and one; every nonzero coefficient at position k satisfies k+3 at most p. div denotes natural integer quotient.

**Theorem 1.3 (Strict tail bound and positive endpoint).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall T \in \mathbb{Z},\; \left(0 < m \land \operatorname{markedPrefix}\left(n, m, p, T\right)\right) \Rightarrow \left(\operatorname{abs}\left(T\right) < \operatorname{cast}\left(2^{\operatorname{NatSub}\left(p, 2\right)}, \mathbb{Z}\right) \land 0 < n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic.marked_prefix_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonempty marked block dominates the separated signed tail. Bounded signed-list evaluation gives the strict absolute tail bound, including positions below three where the tail vanishes, and the lowest positive marked summand forces the endpoint to be positive. NatSub is truncated natural subtraction.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic.markedPowers`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic.markedPrefix`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic.marked_prefix_tail_bound`
