# The proposed stochastic generator set misses a six-cycle matrix

## Abstract

A column-stochastic matrix with six-cycle support cannot be obtained from the generators of Eq. (10).

All matrices are real and have rows and columns indexed by Fin 3, namely 0, 1, 2. The symbol 1 denotes the identity matrix. A column-stochastic matrix has nonnegative entries and each column sums to one; these conditions are written out in claim.

**Definition 1.1 (The first vertex of Eq. (10)).**

$$(V1: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)) = \begin{bmatrix}1&0&1\\0&1&0\\0&0&0\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.V1` (`✓ std3`).

*Citation.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

The first nonidentity vertex sends coordinates 0 and 2 to coordinate 0 and fixes coordinate 1.

**Definition 1.2 (The second vertex of Eq. (10)).**

$$(V2: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)) = \begin{bmatrix}1&0&1\\0&0&0\\0&1&0\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.V2` (`✓ std3`).

*Citation.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

The second nonidentity vertex sends coordinates 0 and 2 to coordinate 0 and sends coordinate 1 to coordinate 2.

**Definition 1.3 (The cyclic vertex of Eq. (10)).**

$$(V3: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)) = \begin{bmatrix}0&0&1\\1&0&0\\0&1&0\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.V3` (`✓ std3`).

*Citation.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

The third nonidentity vertex is the cyclic permutation matrix sending 0 to 1, 1 to 2, and 2 to 0.

**Definition 1.4 (The transposition in Eq. (10)).**

$$(swap12: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)) = \begin{bmatrix}0&1&0\\1&0&0\\0&0&1\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.swap12` (`✓ std3`).

*Citation.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

The transposition interchanges coordinates 0 and 1 and fixes coordinate 2.

**Definition 1.5 (The proposed generator set).**

$$gen = \left\{swap12\right\} \cup convexHull\left(\mathbb{R}, \left\{(1: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)), V1, V2, V3\right\}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.gen` (`✓ std3`).

*Citation.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

Equation (10) takes the union of the singleton containing swap12 and the real convex hull of the identity and V1, V2, V3. A convex combination has nonnegative real weights summing to one.

**Definition 1.6 (Products of a fixed number of generators).**

$$(genPow\left(0\right) = \left\{(1: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right))\right\}) \land (\forall (m: \mathbb{N}), (genPow\left(m + 1\right) = \{(A: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)) \mid \exists (g: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)), ((g \in gen) \land (\exists (w: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)), ((w \in genPow\left(m\right)) \land (A = g \cdot w))))\}))$$

*Formalization.* `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.genPow` (`✓ std3`).

*Citation.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

The set genPow(m) consists of products of exactly m elements of gen, with repetitions allowed. Zero factors give the identity. Each additional factor multiplies a shorter product on the left. This is the product length used in Definition 3.

**Definition 1.7 (The proposed optimal length twenty).**

$$(claim) \Leftrightarrow ((\forall (A: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)), (((\forall (i: Fin\left(3\right)), (\forall (j: Fin\left(3\right)), (0 \le A\left(i, j\right)))) \land (\forall (j: Fin\left(3\right)), (\sum_{(i: Fin\left(3\right))} A\left(i, j\right) = 1))) \Rightarrow (A \in genPow\left(20\right)))) \land (\exists (A: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{R}\right)), (((\forall (i: Fin\left(3\right)), (\forall (j: Fin\left(3\right)), (0 \le A\left(i, j\right)))) \land (\forall (j: Fin\left(3\right)), (\sum_{(i: Fin\left(3\right))} A\left(i, j\right) = 1))) \land (\neg (A \in genPow\left(19\right))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.claim` (`✓ std3`).

*Citation.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

Theorem 3 asserts that every column-stochastic 3 by 3 matrix is a product of twenty elements of the set in Eq. (10). The conjecture in Section 4 asserts optimality: some column-stochastic matrix is not a product of nineteen. Since the identity belongs to gen, shorter products can be padded with identity factors, so the two clauses express the proposed optimal length twenty.

**Theorem 1.8 (A six-cycle matrix contradicts the twenty-factor assertion).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/vom-ende-shahbeigi-2024-stochastic-generator-set-refutation` (refuted) by `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vom-ende-shahbeigi-2024-stochastic-generator-set-refutation","declaration_gid":"D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende; Fereshte Shahbeigi (2024). *Generating Sets of Stochastic Matrices*. URL: <https://arxiv.org/abs/2411.18946v2>.

*Commentary.*

Take A = [[1/4, 0, 1/4], [3/4, 1/2, 0], [0, 1/2, 3/4]]. Its entries are nonnegative and every column sums to one. Its positive entries form the bipartite six-cycle row 0, column 0, row 1, column 1, row 2, column 2, row 0.

A has the following indivisibility property: if B and C are column-stochastic and their product is a row and column permutation of A, then B or C is a permutation matrix. For each intermediate coordinate, the positive entries of the corresponding column of B and row of C form a rectangle in the support of the product. The six-cycle contains no rectangle with two rows and two columns. Covering its six edges by three rectangles therefore gives three stars centred at the three rows or at the three columns. Column normalization makes one factor a permutation matrix.

No row and column permutation of A belongs to gen. Such a matrix has six positive entries, whereas swap12 has three. The convex hull has zeros at positions (0,1), (1,2), (2,0) and weakly decreasing diagonal entries. None of the thirty-six row and column permutations of A satisfies all these conditions. If a permuted A were a finite product from gen, indivisibility would let permutation factors be removed until a row and column permutation of A belonged to gen, a contradiction. In particular A is not a product of twenty generators, so claim is false.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.V1`
- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.V2`
- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.V3`
- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.gen`
- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.genPow`
- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.swap12`
- Dependency: [D5/S3/Quantum/Matrix/ProjectionAMGMRefutation](ProjectionAMGMRefutation.md)
