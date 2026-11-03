# The uniform residual polynomial

## Abstract

The exact residual count satisfies Gupta's total degree bound.

Gupta, arXiv:2607.05567v3, Conjecture 8.3 asks that the remainder for each positive split a+b=d, a at most b, have total degree at most d-3 when d is at least five. Lemma 8.2 identifies one polynomial on every rectangle with m,n at least 2d-1. The remainder counts precisely the normalized integer unit-edge height functions whose strict minima do not all lie on one common physical side.

**Theorem 1.1 (Cardinality of each actual fiber).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraResolution.fiber_card_eq_positive_vectors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraResolution.fiber_card_eq_positive_vectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For all natural a,b,m,n, every K in Core a b, and m,n at least 2(a+b)-1, Nat.card of Fiber a b m n K equals Nat.card of the product PositiveLengths (m-rowOccupied K) (rowRuns K) and PositiveLengths (n-colOccupied K) (colRuns K). The actual equivalence core_positive_vectors_equiv has precisely this fiber as its target, including the complete original height function, JointReduction and the equivalence for every individual physical side. Nat.card_congr therefore applies directly; no quotient, selection of representatives or cardinality assumption is introduced.

**Theorem 1.2 (The same polynomial counts the original arrays).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraResolution.core_polynomial_counts_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraResolution.core_polynomial_counts_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For all natural a,b,m,n with a,b positive, a+b at least five, and m,n at least 2(a+b)-1, evaluation of corePolynomial a b at the rational pair (m,n) equals the rational cast of the unchanged residualCount a b m n. The actual partition residualCoreEquiv places every array in exactly one actual Core fiber. residual_count_eq_sum_fibers gives the sum of these cardinalities. The fiber equality above identifies that sum with core_polynomial_eval. Its positive-vector evaluations use positive_lengths_card and the existing binomial polynomial identities, with all feasibility bounds proved for these same cores.

**Theorem 1.3 (The complete original polynomial assertion).**

$$\forall d \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (5 \le d) \Rightarrow \left((1 \le a) \Rightarrow \left((1 \le b) \Rightarrow \left((a + b = d) \Rightarrow \left((a \le b) \Rightarrow \left(\exists p \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{Q}\right),\; (\operatorname{totalDegree}\left(p\right) \le d - 3) \land (\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; (2 \cdot d - 1 \le m) \Rightarrow \left((2 \cdot d - 1 \le n) \Rightarrow \operatorname{eval}\left((\lambda (i:\operatorname{Fin}\left(2\right)) \mapsto \operatorname{ite}\left(i = 0, (m:\mathbb{Q}), (n:\mathbb{Q})\right)), p\right) = (\operatorname{residualCount}\left(a, b, m, n\right):\mathbb{Q})\right))\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraResolution.result` (`✓ std3`). ∎

*Resolves.* `Problems/gupta-2026-miura-residual-degree-conjecture-83` (proved) by `D5/S3/Combinatorics/Geometry/MiuraResolution.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gupta-2026-miura-residual-degree-conjecture-83","declaration_gid":"D5/S3/Combinatorics/Geometry/MiuraResolution.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

For every natural d at least five and positive natural a,b with a+b=d and a at most b, there exists a rational bivariate polynomial of total degree at most d-3 which counts the exact residual class for every natural m,n at least 2d-1. The polynomial is corePolynomial a b, a finite sum over the individual bounded actual cores; it is chosen before either evaluation dimension. core_polynomial_degree_le gives its strict total degree bound, and core_polynomial_counts_residual supplies every evaluation. The argument also establishes the evaluations without using the order of a and b; the conclusion retains the original ordered-split condition.

Here residualCount counts every individual function h from Fin m times Fin n to the integers with h(0,0)=0 and absolute difference exactly one across each Manhattan edge. Strict minima and maxima test all existing neighbours, including the two neighbours of a corner and the three neighbours of a noncorner boundary cell. Their exact cardinalities are a and b. The condition is the negation of the existence of one common side containing every minimum: top has first coordinate one, bottom first coordinate m, left second coordinate one, and right second coordinate n in physical coordinates. A corner belongs to both incident sides. The condition permits minima on several boundary sides and introduces no symmetry quotient or orientation identification.

In the formula, eval uses the assignment i to m if i=0 and to n otherwise, with both dimensions cast to the rationals. The count also has its rational cast. All subtractions in the dimension and degree bounds are natural-number subtractions.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResolution.core_polynomial_counts_residual`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResolution.fiber_card_eq_positive_vectors`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraResolution.result`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberEquiv](MiuraFiberEquiv.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraPartitionCount](MiuraPartitionCount.md)
