# Fixed-point-free permutation solutions of the n-simplex equation

## Abstract

For n > 2, a permutation without fixed points gives a solution of the n-simplex equation on every set exactly when n is even, and then the product of the transpositions of adjacent pairs of indices is such a solution. This answers Question 2 of V. Bardakov, B. Chuzinov, I. Emel'yanenkov, M. Ivanov, T. Kozlovskaya and V. Leshkov (arXiv:2206.08906; Question 4.22 of the journal version).

**Definition 1.1 (The coordinates).**

$$\operatorname{Edge}\left(n\right) = \{(a, b) \in \mathbb{N} \times \mathbb{N} : (a < b) \land b \le n\}$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.Edge` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

The n-simplex equation acts on X^N with N = n(n+1)/2 coordinates, indexed by the edges {a, b}, a < b <= n, of the complete graph on the vertices 0, ..., n of the n-simplex. The paper numbers the coordinates by the rows of its matrix MI_n; row v of MI_n lists the edges at the vertex v in increasing order of the other endpoint, which is the order used below.

**Definition 1.2 (The edges at a vertex).**

$$\operatorname{slotEdge}\left(v, j\right) = \operatorname{ite}\left(j < v, (j, v), (v, j + 1)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.slotEdge` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

For a vertex v in Fin (n + 1) and a slot j in Fin n, slotEdge(v, j) is the edge from v to the j-th of the other n vertices in increasing order: the vertex j when j < v, and j + 1 otherwise.

**Definition 1.3 (The vertex operators).**

$$\operatorname{opR}\left(T, v, x\right)\left(e\right) = \operatorname{ite}\left(e_{1} = v, T\left((j \mapsto x\left(\operatorname{slotEdge}\left(v, j\right)\right))\right)\left(e_{2} - 1\right), \operatorname{ite}\left(e_{2} = v, T\left((j \mapsto x\left(\operatorname{slotEdge}\left(v, j\right)\right))\right)\left(e_{1}\right), x\left(e\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.opR` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

For a map T from X^n to itself, R_v(T) applies T to the n coordinates on the edges at v, taken in slot order, and leaves the other coordinates unchanged. An edge (a, b) at v is in slot b - 1 when a = v and in slot a when b = v.

**Definition 1.4 (The left side).**

$$\operatorname{lhs}\left(T, 0\right) = \operatorname{id},\qquad\operatorname{lhs}\left(T, k + 1\right) = \operatorname{lhs}\left(T, k\right) \circ \operatorname{opR}\left(T, k\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.lhs` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

lhs(T, k) is the composition R_0(T) R_1(T) ... R_(k-1)(T) of the first k vertex operators, so that R_(k-1)(T) acts first; operators of vertices k > n are omitted.

**Definition 1.5 (The right side).**

$$\operatorname{rhs}\left(T, 0\right) = \operatorname{id},\qquad\operatorname{rhs}\left(T, k + 1\right) = \operatorname{opR}\left(T, k\right) \circ \operatorname{rhs}\left(T, k\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.rhs` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

rhs(T, k) is the composition R_(k-1)(T) ... R_1(T) R_0(T) of the same operators in the reverse order.

**Definition 1.6 (The n-simplex equation).**

$$\operatorname{IsSolution}\left(n, T\right) \Leftrightarrow (\operatorname{lhs}\left(T, n + 1\right) = \operatorname{rhs}\left(T, n + 1\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.IsSolution` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

T is a solution of the n-simplex equation when R_0 R_1 ... R_n = R_n ... R_1 R_0 as maps of X^N, as in the paper. The two sides are mutually reverse words, so the equation does not depend on the convention for applying a written product of operators.

**Definition 1.7 (Simple maps).**

$$\operatorname{simpleMap}\left(s, y\right)\left(j\right) = y\left(s\left(j\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.simpleMap` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

For a map s from Fin n to itself, the simple map of s sends (x_1, ..., x_n) to (x_s(1), ..., x_s(n)).

**Definition 1.8 (Question 2).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N}, 2 < n \Rightarrow ((\exists s \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right), (\forall i, s\left(i\right) \ne i) \land \forall X, \operatorname{IsSolution}\left(n, \operatorname{simpleMap}\left(s\right)\right)) \Leftrightarrow (\operatorname{Even}\left(n\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.claim` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

Question 2 of the paper asks: for which n > 2 are there non-identity permutations without fixed points that give solutions of the n-simplex equation? The statement answers it: such a permutation s of Fin n exists, with the simple map of s a solution on every type X, exactly when n is even. Here Perm(Fin n) is Equiv.Perm (Fin n) and Even is Nat's Even.

**Theorem 1.9 (Exactly the even n).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.result` (`✓ std3`). ∎

*Resolves.* `Problems/bardakov-2024-simplex-fixed-point-free-permutations` (proved) by `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bardakov-2024-simplex-fixed-point-free-permutations","declaration_gid":"D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

The simple map of s acts on the coordinates by permuting edges: R_v(T_s) x = x composed with the map sigma_v that sends the edge in slot j at v to the edge in slot s(j) at v. So the two sides are x composed with sigma_n ... sigma_0 and with sigma_0 ... sigma_n, and T_s is a solution on every type exactly when these two edge maps agree. Following the edge {i, i+1} through the vertices in increasing and in decreasing order gives the edges {s(i), s(i)+1} or {s(i), i}, and {s(i), s(i)+1} or {i+1, s(i)+1}; they agree only when |s(i) - i| <= 1. Conversely, if every index moves by at most one, every edge reaches the same edge in both orders, in one of three closed forms. A permutation without fixed points that moves every index by one has displacements s(i) - i equal to +1 or -1 with sum 0, so n, the sum of the even numbers s(i) - i + 1, is even. For even n the involution exchanging 2t and 2t + 1 has no fixed point and moves every index by one, so its simple map is a solution.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.Edge`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.IsSolution`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.lhs`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.opR`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.result`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.rhs`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.simpleMap`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.slotEdge`
