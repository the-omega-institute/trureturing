# Ganguly Question 9.2 on 1-sums and bridge joins

## Abstract

The same two looped multigraphs disprove both closure laws over each field in Question 9.2.

**Definition 1.1 (Graphical symplectic representability).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.Representable`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.Representable` (`✓ std3`).

*Citation.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

For a finite multigraph G and field F, there is a row number k equal to the maximum size of a Chow-independent admissible signed edge selection. There is a k-row matrix over F with independent rows and columns indexed by edges paired with their starred copies. The alternating pairing of every pair of rows is zero. For every injective list of k edge IDs with a Boolean mark per entry, the corresponding k-column minor has nonzero determinant exactly when the selection is Chow independent. Each spanning component must be a tree or unicyclic with odd star parity on its unique cycle. Connectivity ignores endpoint orientation. A cycle is a nonempty connected 2-regular edge subset, counting both incidences of a loop.

**Definition 1.2 (Triangle with two loops).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.factorOne`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.factorOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

The five edge IDs have endpoints (0,1), (1,2), (2,0), (0,0), and (1,1), in order.

**Definition 1.3 (One vertex with one loop).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.factorTwo`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.factorTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

The single edge is a loop at vertex 0.

**Definition 1.4 (Rooted 1-sum).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.oneSumAt`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.oneSumAt` (`✓ std3`).

*Citation.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

The inputs have n and m + 1 vertices, respectively, with one selected vertex each. On the right, exchange the selected vertex with the last label. Send that last label to the chosen left vertex and place the other m labels after the n left vertices. Append the edge IDs, transporting both endpoint maps.

**Definition 1.5 (Rooted bridge join).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.bridgeAt`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.bridgeAt` (`✓ std3`).

*Citation.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

Place all right vertices after the left vertices and append the right edge IDs after the left edge IDs. Append one fresh edge from the chosen left vertex to the chosen right vertex.

**Definition 1.6 (The 1-sum witness).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.oneSum`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.oneSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

Form the rooted 1-sum of the two factors at left vertex 2 and right vertex 0. The resulting graph is a triangle with a loop at every vertex.

**Definition 1.7 (The bridge-join witness).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.bridgeJoin`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.bridgeJoin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

Join the same roots of the disjoint factors by a fresh edge. The loop at vertex 3 belongs to the right factor, and the fresh edge is the edge of ID 6.

**Definition 1.8 (Affirmative closure assertion).**

Lean statement: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.claim`

*Formalization.* `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.claim` (`✓ std3`).

*Citation.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

Question 9.2 (arXiv:2611.01241v2, printed p. 39) asks “Over fields of characteristic 2 with at least 4 elements, is representability of 𝒮(G) preserved under 1-sums and under joining two graphs by a bridge?”

There exists a field F in Lean's Type universe (level zero) of characteristic two with an embedding of Fin 4 into F, over which at least one of the two closure laws holds. A closure law quantifies over all pairs of finite rooted multigraphs, encoded by arbitrary finite vertex and edge cardinalities, and both root choices. If both input graphs are representable over F, the corresponding join must be representable over F.

**Theorem 1.9 (Counterexamples over each qualifying field).**

$$\forall F \in \mathrm{Type}\,u,\; Field\left(F\right) \Rightarrow \left(CharP\left(F, 2\right) \Rightarrow \left(Nonempty\left(Embedding\left(Fin\left(4\right), F\right)\right) \Rightarrow \left(\left(Representable\left(F, factorOne\right) \land Representable\left(F, factorTwo\right)\right) \land \left(\left(\neg Representable\left(F, oneSum\right)\right) \land \left(\neg Representable\left(F, bridgeJoin\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.question_nine_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

For any universe level u and any field F in Type u of characteristic two with an embedding of Fin 4 into F, both factors are representable and each of their two joins is nonrepresentable.

The rank-three matrix uses a parameter distinct from zero and one. Its basis minors depend affinely on that parameter. Finite determinant checks at zero and one recover the full signed basis condition by scalar transport and interpolation. The rank-one matrix has unstarred column zero and starred column one.

The three starred loops in the 1-sum form a basis. Finite signed-basis checks force each marked triangle edge into its endpoint plane with both coefficients nonzero. The even-star tests force the three gain ratios to coincide and square to one. In characteristic two the common ratio equals one, contradicting a one-star test.

Checking every signed selection establishes that adjoining the unstarred bridge preserves Chow independence under contraction. Its column is nonzero by the lifted loop basis. Quotienting by its span transfers the signed-basis conditions to the same triangle obstruction.

**Theorem 1.10 (Refutation of both closure laws).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sayantan Ganguly (2026). *Representability of Graphical Symplectic Matroids*. DOI: [10.48550/arXiv.2611.01241](https://doi.org/10.48550/arXiv.2611.01241). URL: <https://arxiv.org/abs/2611.01241v2>.

*Commentary.*

Apply the asserted closure law to the two representable factors at the specified roots. The field-uniform witness contradicts representability of the selected output in either case.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.Representable`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.bridgeAt`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.bridgeJoin`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.factorOne`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.factorTwo`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.oneSum`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.oneSumAt`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.question_nine_two`
- Truth anchor: `D5/S3/Combinatorics/Matroids/GangulyQuestionNineTwo.result`
- Dependency: [D5/S3/ConceptDynamics/Coding/EssentialWordRealization](../../ConceptDynamics/Coding/EssentialWordRealization.md)
