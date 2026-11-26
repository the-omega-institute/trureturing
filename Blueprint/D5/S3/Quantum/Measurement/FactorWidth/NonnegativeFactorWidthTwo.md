# Nonnegative real factors from complex two-sparse factors

## Abstract

Entrywise nonnegative matrices of complex factor width at most two admit bounded nonnegative real decompositions.

**Theorem 1.1 (Bounded nonnegative two-sparse Gram decomposition).**

$$\forall (n : \mathbb{N}), \forall (X : \operatorname{Matrix}(\operatorname{Fin}(n), \operatorname{Fin}(n), \mathbb{R})), (\forall (i : \operatorname{Fin}(n)), \forall (j : \operatorname{Fin}(n)), 0 \leq X(i,j)) \to \operatorname{IsKIncoherentSum}(2, \operatorname{complex}(X)) \to \exists (k : \mathbb{N}), \exists (v : \operatorname{Fin}(k) \to \operatorname{Fin}(n) \to \mathbb{R}), k \leq n + \operatorname{choose}(n, 2) \land (\forall (t : \operatorname{Fin}(k)), \forall (i : \operatorname{Fin}(n)), 0 \leq v_{t}(i)) \land (\forall (t : \operatorname{Fin}(k)), \operatorname{card}(\operatorname{supp}(v_{t})) \leq 2) \land X = \sum_{t \in \operatorname{Fin}(k)} v_{t} v_{t}^{T}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FactorWidth/NonnegativeFactorWidthTwo.nonnegative_two_sparse_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is a real square matrix X with nonnegative entries. Its entrywise complex coercion admits a finite sum of complex Hermitian outer products, each on at most two coordinates. The conclusion preserves the full matrix and bounds the number of entrywise nonnegative real factors, each supported on at most two coordinates.

Group the input factors by exact two-element support. For one pair, let A and B be the sums of squared norms at its endpoints and let c be the corresponding entry of X. Cauchy–Schwarz gives c squared at most A times B. For A positive, use the entries sqrt(A) and c / sqrt(A). For A zero, c is zero and the pair can contribute zero. The new factor preserves the cross entry and consumes at most each diagonal budget.

Exact support groups are disjoint, so total diagonal consumption is at most the original diagonal. One singleton factor at each vertex supplies the difference. This uses one slot per unordered pair and one per vertex, allowing zero factors.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FactorWidth/NonnegativeFactorWidthTwo.nonnegative_two_sparse_gram`
- Dependency: [D5/S3/Quantum/Measurement/FactorWidthTwoCone](../FactorWidthTwoCone.md)
