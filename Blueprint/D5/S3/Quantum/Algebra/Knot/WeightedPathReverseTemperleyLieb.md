# Reverse Adjacent Law for Weighted Path Projections

## Abstract

Reversal of the actual fixed-endpoint legal paths supplies the missing reverse adjacent Temperley-Lieb relation.

**Theorem 1.1 (Reversing the two endpoint fibers).**

$$\begin{gathered}\operatorname{FiniteDecidable}\left(L\right); \operatorname{SymmetricPositivePerronData}\left(R, d, delta\right)\\\forall n \in \mathbb{N},\; \forall s \in L,\; \forall t \in L,\; \forall i \in \mathbb{N},\; \operatorname{And}\left(\operatorname{Lt}\left(0, i\right), \operatorname{Lt}\left(i+1, n\right)\right)\Rightarrow \operatorname{P}\left(n, s, t, i+1\right) \cdot \operatorname{P}\left(n, s, t, i\right) \cdot \operatorname{P}\left(n, s, t, i+1\right) = \operatorname{SMul}\left(\operatorname{Pow}\left(\operatorname{Inv}\left(delta\right), 2\right), \operatorname{P}\left(n, s, t, i+1\right)\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/WeightedPathReverseTemperleyLieb.weighted_path_reverse_temperley_lieb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be a finite decidable type, R a decidable symmetric relation, d strictly positive real vertex weights, and delta a strictly positive real number. Assume the Perron equality: for every a, the sum of d(b) over all b related to a is delta times d(a). For every n, both endpoints s and t, and every index with zero less than i and i+1 less than n, let P_i be the literal pathProjection of WeightedLegalPathTemperleyLieb on LegalPath R n s t. Then P_(i+1) P_i P_(i+1) is the complex square of delta inverse times P_(i+1). Empty endpoint fibers remain included; the index range is empty when n is less than three.

The existing supplier proves the forward adjacent law, P_i P_(i+1) P_i = delta inverse squared times P_i. Taking an adjoint repeats that same law and does not yield the reverse one. Instead, reverse every coordinate using Fin.rev. Symmetry of R makes the reversed sequence legal, exchanges s and t, and gives a genuine involutive equivalence of the two endpoint fibers.

Under this equivalence the literal local kernel at n-i pulls back to the kernel at i. The away-from-i guard is transported along the reverse coordinate bijection. The two flanks exchange places. On the support of the kernel those flank labels agree, so their weights and the denominator agree; no additional symmetry assumption on d is used. Off the support both entries are zero. Matrix.submatrix_mul_equiv transports the forward law at n-(i+1) on the reversed endpoint fiber into the required reverse law on the original fiber.

This is classical Temperley-Lieb path-model mathematics. Aharonov, Jones and Landau, A Polynomial Quantum Algorithm for Approximating the Jones Polynomial, arXiv:quant-ph/0511096v2, Definition 2.2 specifies both adjacent directions; Definition 3.2 and Claim 3.1 give the line-graph path representation. The present proof reuses the repository's arbitrary finite symmetric-relation supplier and its positive Perron data. Its endpoint reversal is a reusable algebraic coordinate equivalence, not a geometric reflection of knots.

The reverse relation fills an actual missing hypothesis for the subsequent Artin braid representation. Together with the existing idempotence and distant commutation laws it supplies both adjacent directions. This unit does not yet construct that representation, identify geometric braid closure or prove geometric Markov equivalence. It does not settle Laurent integrality, modular specialization, an explicit knot witness or the open knot target.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Knot/WeightedPathReverseTemperleyLieb.weighted_path_reverse_temperley_lieb`
- Dependency: [D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb](../WeightedLegalPathTemperleyLieb.md)
