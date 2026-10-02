# A regular biconnected graph with a positive fourth difference of ln(i! N(i))

## Abstract

Butera, Federbush and Pernici (arXiv:1502.06734) ask whether the bounds Delta^k ln(i! N(i)) <= 0 for k <= 4 always hold for regular biconnected graphs, where N(i) counts the configurations of i dimers. They do not: a 6-regular biconnected graph on 28 vertices, made of four copies of K_7 minus an edge joined in a ring, has a positive fourth difference at i = 10.

**Definition 1.1 (Dimer configurations).**

$$\forall n : \mathbb{N}, \forall G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \forall i : \mathbb{N}, \operatorname{matchingCount}\left(G, i\right) = \operatorname{card}\left(\ \{M \mid M \in \operatorname{Matching}\left(n, i\right), M \subseteq \operatorname{edgeSet}\left(G\right)\ \}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.matchingCount` (`✓ std3`).

*Citation.* Paolo Butera; Paul Federbush; Mario Pernici (2015). *Positivity of the virial coefficients in lattice dimer models and upper bounds on the number of matchings on graphs*. DOI: [10.1016/j.physa.2015.05.106](https://doi.org/10.1016/j.physa.2015.05.106). URL: <https://arxiv.org/abs/1502.06734v2>.

*Commentary.*

N(i) is the number of configurations of i dimers on G, that is, of sets of i pairwise vertex-disjoint edges of G. Here Matching(n, i) is the set of sets of i unordered, loop-free, pairwise vertex-disjoint pairs of vertices of Fin(n), and N(G, i) is the number of its elements all of whose pairs are edges of G.

**Definition 1.2 (The matching number).**

$$\forall n : \mathbb{N}, \forall G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{matchingNumber}\left(G\right) = \operatorname{sSup}\left(\ \{i \mid i \in \mathbb{N}, 0 < \operatorname{matchingCount}\left(G, i\right)\ \}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.matchingNumber` (`✓ std3`).

*Citation.* Paolo Butera; Paul Federbush; Mario Pernici (2015). *Positivity of the virial coefficients in lattice dimer models and upper bounds on the number of matchings on graphs*. DOI: [10.1016/j.physa.2015.05.106](https://doi.org/10.1016/j.physa.2015.05.106). URL: <https://arxiv.org/abs/1502.06734v2>.

*Commentary.*

The matching number nu(G) is the maximum number of pairwise disjoint edges of G; it is the supremum of the i with N(G, i) > 0.

**Definition 1.3 (Biconnected graphs).**

$$\forall V : \operatorname{Type}, \forall G : \operatorname{SimpleGraph}\left(V\right), (\operatorname{Biconnected}\left(G\right)) \Leftrightarrow ((\operatorname{Connected}\left(G\right)) \land (\forall v : V, \operatorname{Connected}\left(\operatorname{induce}\left(\operatorname{compl}\left(\ \{v\ \}\right), G\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.Biconnected` (`✓ std3`).

*Citation.* Paolo Butera; Paul Federbush; Mario Pernici (2015). *Positivity of the virial coefficients in lattice dimer models and upper bounds on the number of matchings on graphs*. DOI: [10.1016/j.physa.2015.05.106](https://doi.org/10.1016/j.physa.2015.05.106). URL: <https://arxiv.org/abs/1502.06734v2>.

*Commentary.*

A graph is biconnected when it is connected and remains connected after deleting any one vertex: the subgraph induced on the complement of {v} is connected for every vertex v.

**Definition 1.4 (The question for k at most 4).**

$$(claim) \Leftrightarrow (\forall n : \mathbb{N}, \forall G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right), (\exists d : \mathbb{N}, \operatorname{IsRegularOfDegree}\left(G, d\right)) \Rightarrow ((\operatorname{Biconnected}\left(G\right)) \Rightarrow (\forall k : \mathbb{N}, \forall i : \mathbb{N}, (2 \le k) \Rightarrow ((k \le 4) \Rightarrow ((i + k \le \operatorname{matchingNumber}\left(G\right)) \Rightarrow ((\Delta^{k} (j\mapsto\operatorname{log}\left(j! \cdot \operatorname{matchingCount}\left(G, j\right)\right)))\left(i\right) \le 0))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.claim` (`✓ std3`).

*Citation.* Paolo Butera; Paul Federbush; Mario Pernici (2015). *Positivity of the virial coefficients in lattice dimer models and upper bounds on the number of matchings on graphs*. DOI: [10.1016/j.physa.2015.05.106](https://doi.org/10.1016/j.physa.2015.05.106). URL: <https://arxiv.org/abs/1502.06734v2>.

*Commentary.*

The paper's Eq. (1) is Delta^k ln(i! N(i)) <= 0 for k = 2, ..., nu and i = 0, ..., nu - k, with Delta the forward difference in i, and its Section IV B asks whether these bounds for k <= 4 are always satisfied for regular biconnected graphs. The displayed statement reads the question as a universal statement over finite simple graphs on Fin(n): regularity is the existence of a common degree d, and Delta^k is the k-th iterate of the forward difference with step 1. For k = 2 the bound follows from the Heilmann-Lieb inequality.

**Theorem 1.5 (The answer is negative).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/butera-2015-dimer-virial-bounds-regular-biconnected` (refuted) by `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"butera-2015-dimer-virial-bounds-regular-biconnected","declaration_gid":"D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paolo Butera; Paul Federbush; Mario Pernici (2015). *Positivity of the virial coefficients in lattice dimer models and upper bounds on the number of matchings on graphs*. DOI: [10.1016/j.physa.2015.05.106](https://doi.org/10.1016/j.physa.2015.05.106). URL: <https://arxiv.org/abs/1502.06734v2>.

*Commentary.*

Take the graph on the 28 vertices x = 7b + t, with block b in {0, 1, 2, 3} and position t in {0, ..., 6}: inside a block all pairs of vertices are adjacent except positions 0 and 1, and position 1 of block b is adjacent to position 0 of block b + 1 modulo 4. Every vertex has degree 6. Visiting positions 0, 2, 3, 4, 5, 6, 1 of blocks 0, 1, 2, 3 in turn is a Hamiltonian cycle, and deleting one vertex from it leaves a Hamiltonian path of the other vertices, so the graph is biconnected. For an edge e of an edge set E, the (i + 1)-matchings of E either avoid e or contain it, so N(E, i + 1) = N(E - e, i + 1) + N(E_e, i), where E_e is the set of edges of E disjoint from e; for two edge sets without a common vertex the matching sequence of the union is the Cauchy product of the two sequences. The first rule applied to the four connecting edges and the second to the four blocks reduce the count to the matching sequences of K_7 minus an edge, K_6 and K_5, which are (1, 20, 95, 90), (1, 15, 45, 15) and (1, 10, 15). This gives N(10) = 845745750, N(11) = 506745000, N(12) = 141530625, N(13) = 9922500 and N(14) = 101250, and nu = 14 because 28 vertices carry at most 14 disjoint edges. With A_i = i! N(i), the fourth difference of ln A at i = 10 is ln(A_10 A_12^6 A_14) - ln(A_11^4 A_13^4), which is positive because A_11^4 A_13^4 < A_10 A_12^6 A_14 as integers. So k = 4 and i = 10, with i + k = nu, violate the bound.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.Biconnected`
- Truth anchor: `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.matchingCount`
- Truth anchor: `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.matchingNumber`
- Truth anchor: `D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.result`
- Dependency: [D5/S3/Zeros/Convolution/MatchingFiber](../Zeros/Convolution/MatchingFiber.md)
