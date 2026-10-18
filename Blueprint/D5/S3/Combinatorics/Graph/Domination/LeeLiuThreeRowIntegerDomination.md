# Integer {2}-domination of three-row grids

## Abstract

The integer {2}-domination number of the three-row Cartesian grid is ⌊3n/2⌋ + 1 for every positive n. A potential on pairs of three-entry columns gives the lower bound, and alternating columns attain it.

**Definition 1.1 (The Cartesian grid).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \operatorname{grid}\left(m, n\right) = \operatorname{SimpleGraph}.\operatorname{boxProd}\left(\operatorname{SimpleGraph}.\operatorname{pathGraph}\left(m\right), \operatorname{SimpleGraph}.\operatorname{pathGraph}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.grid` (`✓ std3`).

*Citation.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

Lee and Liu, Section 1 (p. 2): "For positive integers m and n, the grid graph Gm,n = Pm □ Pn is the Cartesian product of path graphs Pm and Pn." The pair (i,j) in Fin m × Fin n represents the vertex v at row i+1 and column j+1. The operation □ is SimpleGraph.boxProd, and SimpleGraph.pathGraph joins consecutive indices.

**Definition 1.2 (Integer {2}-dominating functions).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (f : (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{N}), (\operatorname{IsTwoDominating}\left(m, n, f\right)) \Leftrightarrow ((\forall (v : \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), f\left(v\right) \le 2) \land (\forall (v : \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), 2 \le f\left(v\right) + \sum_{u \in \operatorname{SimpleGraph}.\operatorname{neighborFinset}\left(\operatorname{grid}\left(m, n\right), v\right)} f\left(u\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.IsTwoDominating` (`✓ std3`).

*Citation.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

Lee and Liu, Abstract (p. 1): "An integer {2}-dominating function of a graph is a mapping from the vertex set to {0, 1, 2} such that the sum of the mapped values of each vertex and its neighbors is at least 2; the integer {2}-domination number of a graph is defined to be the minimum sum of mapped values of all vertices among all integer {2}-dominating functions." A natural-number value bounded by 2 is in {0,1,2}. The sum uses the open neighbour set and adds f(v) once, giving precisely the closed-neighbourhood sum. Section 1 allows all nonnegative integer values; truncation at 2 preserves feasibility and cannot increase weight.

**Definition 1.3 (The minimum weight).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \operatorname{gamma2}\left(m, n\right) = \operatorname{sInf}\left(\{w : \mathbb{N} \mid \exists (f : (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{N}), (\operatorname{IsTwoDominating}\left(m, n, f\right)) \land (\sum_{v : \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)} f\left(v\right) = w)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.gamma2` (`✓ std3`).

*Citation.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

Lee and Liu, Abstract (p. 1): "An integer {2}-dominating function of a graph is a mapping from the vertex set to {0, 1, 2} such that the sum of the mapped values of each vertex and its neighbors is at least 2; the integer {2}-domination number of a graph is defined to be the minimum sum of mapped values of all vertices among all integer {2}-dominating functions." The natural-number infimum is taken over attained weights. The constant function 2 makes this set nonempty; hence its infimum is its minimum. Every labelled vertex contributes once to the sum.

**Definition 1.4 (Lee–Liu Conjecture 2.5).**

$$(claim) \Leftrightarrow (\forall (n : \mathbb{N}), (1 \le n) \Rightarrow (\operatorname{gamma2}\left(3, n\right) = \operatorname{Nat}.\operatorname{div}\left(3 \cdot n, 2\right) + 1))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.claim` (`✓ std3`).

*Citation.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

Lee and Liu, Conjecture 2.5 (p. 11): "For positive integer n, we have γ{2}(G3,n) = ⌊3n/2⌋ + 1." The row count is 3, the column count ranges over all natural numbers at least 1, and division is natural-number division, written Nat.div. Thus Nat.div (3*n) 2 equals ⌊3n/2⌋.

**Definition 1.5 (Zero-padded columns).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (f : (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{N}), \forall (k : \mathbb{N}), \forall (i : \operatorname{Fin}\left(m\right)), \operatorname{pad}\left(f, k, i\right) = \operatorname{Function}.\operatorname{extend}\left((\operatorname{fun} (j : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Fin}.\operatorname{val}\left(j\right) + 1), (\operatorname{fun} (j : \operatorname{Fin}\left(n\right)) \mapsto f\left((i, j)\right)), (\operatorname{fun} (_ : \mathbb{N}) \mapsto 0), k\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.pad` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

The column with natural index k is extended by zero outside indices 1 through n. Function.extend uses the embedding j ↦ j.val + 1, so the columns at indices 0 and n+1 are zero. The column reduction uses these boundary columns to express the horizontal neighbours.

**Definition 1.6 (The middle-column inequalities).**

$$\forall (m : \mathbb{N}), \forall (a : (\operatorname{Fin}\left(m\right)) \to \mathbb{N}), \forall (b : (\operatorname{Fin}\left(m\right)) \to \mathbb{N}), \forall (c : (\operatorname{Fin}\left(m\right)) \to \mathbb{N}), (\operatorname{ColumnA}\left(m, a, b, c\right)) \Leftrightarrow (\forall (i : \operatorname{Fin}\left(m\right)), 2 \le b\left(i\right) + (\sum_{k \in \operatorname{SimpleGraph}.\operatorname{neighborFinset}\left(\operatorname{SimpleGraph}.\operatorname{pathGraph}\left(m\right), i\right)} b\left(k\right)) + a\left(i\right) + c\left(i\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.ColumnA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

For every row i, the value in the middle column b, its vertical neighbours, and the two horizontal values a(i) and c(i) sum to at least 2. The path graph on Fin m supplies precisely the vertical neighbours, including the endpoint cases.

**Theorem 1.7 (Domination as column inequalities).**

$$\forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (f : (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \to \mathbb{N}), (\forall (v : \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), f\left(v\right) \le 2) \Rightarrow ((\operatorname{IsTwoDominating}\left(m, n, f\right)) \Leftrightarrow (\forall (j : \operatorname{Fin}\left(n\right)), \operatorname{ColumnA}\left(m, \operatorname{pad}\left(f, \operatorname{Fin}.\operatorname{val}\left(j\right)\right), \operatorname{pad}\left(f, \operatorname{Fin}.\operatorname{val}\left(j\right) + 1\right), \operatorname{pad}\left(f, \operatorname{Fin}.\operatorname{val}\left(j\right) + 2\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.column_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

For every row count m and width n, a function bounded by 2 is integer {2}-dominating exactly when each middle column satisfies ColumnA with its two zero-padded neighbours. Splitting the Cartesian-product neighbour set gives the equivalence. The three-row lower bound and the alternating upper construction both use this equivalence.

**Theorem 1.8 (The exact value for every positive width).**

$$\forall (n : \mathbb{N}), (1 \le n) \Rightarrow (\operatorname{gamma2}\left(3, n\right) = \operatorname{Nat}.\operatorname{div}\left(3 \cdot n, 2\right) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.result` (`✓ std3`). ∎

*Resolves.* `Problems/lee-liu-2025-integer-two-domination-three-row` (proved) by `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lee-liu-2025-integer-two-domination-three-row","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jia-Ying Lee; Chia-An Liu (2025). *The integer {2}-domination number of grids*. DOI: [10.48550/arXiv.2502.00134](https://doi.org/10.48550/arXiv.2502.00134). URL: <https://arxiv.org/abs/2502.00134>.

*Commentary.*

A column is encoded by a number in Fin 27. For columns a,b,c the domination condition depends only on those three columns. An integer table R on pairs of columns defines Φ(a,b) = 2s(a)+2s(b)+R(a,b), where s is the column weight. Its initial inequality is Φ(0,b) ≤ 2s(b)−3; every admissible step satisfies Φ(b,c) ≤ Φ(a,b)+2s(c)−3; every terminal pair satisfies 1 ≤ Φ(a,b). Summing gives 1 ≤ 2W−3n, so W ≥ ⌊3n/2⌋+1. The construction of Theorem 2.4 puts (1,1,1) in even columns and (0,1,0) in column 1 and in the last column when n is odd; other columns are zero. For n=1 use (0,2,0). Its weight is exactly ⌊3n/2⌋+1. Together these bounds prove the displayed equality for every n ≥ 1, including the values computed in Remark 2.6.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.ColumnA`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.IsTwoDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.column_reduction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.gamma2`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.grid`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.pad`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.result`
- Dependency: [D5/S1/Digit/MaxDigitSumBase](../../../../S1/Digit/MaxDigitSumBase.md)
- Dependency: [D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap](../../../StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.md)
