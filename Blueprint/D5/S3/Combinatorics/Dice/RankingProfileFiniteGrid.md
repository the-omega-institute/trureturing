# Finite ranking profiles on an ordered grid

## Abstract

Compression and closedness of the finite cubic ranking test.

**Definition 1.1 (Support of a finite weight).**

Lean statement: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.weightSupport`

*Formalization.* `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.weightSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

The support consists of all labels where the weight is nonzero. Disjoint quantized ranges give disjoint supports in quantizedWeights_disjoint.

**Definition 1.2 (Finite probability weights).**

Lean statement: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.IsProbability`

*Formalization.* `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.IsProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

Every weight is nonnegative and the sum over the finite carrier is one. The quantized marginals satisfy these conditions, and finiteWeightLaw_probability uses them to build a probability measure.

**Definition 1.3 (Mass of a decreasing triple).**

Lean statement: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.rankMass`

*Formalization.* `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.rankMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

Sum the products a(x)b(y)c(z) over triples with z < y < x in the finite linear order. sum_rankTuples identifies this sum with a coordinate of the independent product law.

**Definition 1.4 (Six cubic coordinates).**

Lean statement: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.profile`

*Formalization.* `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.profile` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

Apply the decreasing-triple sum to the three weight vectors in the orders XYZ, XZY, YXZ, YZX, ZXY, ZYX. quantizedProfile_eq and finiteProductLaw_realRankProfile use this order for the forward and reverse probability bridges.

**Definition 1.5 (The fifteen-label cubic test).**

$$\forall v \in (\operatorname{Fin}\left(6\right) \to \mathbb{R}),\; v \in \mathit{finiteTest15} \Leftrightarrow \left(\exists a \in (\operatorname{Fin}\left(15\right) \to \mathbb{R}), b \in (\operatorname{Fin}\left(15\right) \to \mathbb{R}), c \in (\operatorname{Fin}\left(15\right) \to \mathbb{R}),\; \left(\left(\left(\left(\left(\operatorname{IsProbability}\left(a\right) \land \operatorname{IsProbability}\left(b\right)\right) \land \operatorname{IsProbability}\left(c\right)\right) \land \operatorname{card}\left(\{i:\operatorname{Fin}\left(15\right) \mid 0 < a\left(i\right)\}\right) \le 5\right) \land \operatorname{card}\left(\{i:\operatorname{Fin}\left(15\right) \mid 0 < b\left(i\right)\}\right) \le 5\right) \land \operatorname{card}\left(\{i:\operatorname{Fin}\left(15\right) \mid 0 < c\left(i\right)\}\right) \le 5\right) \land \operatorname{profile}\left(a, b, c\right) = v\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.finiteTest15` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

A profile passes when three probability weights on the same fifteen ordered labels, each with at most five positive entries, give its six cubic coordinates. finiteTest15_realizable uses the weights to form its finite product law.

**Theorem 1.6 (Closedness of the cubic test).**

$$\operatorname{IsClosed}\left(\mathit{finiteTest15}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.isClosed_finiteTest15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

The capped simplex is a finite union of compact coordinate faces. The cubic profile is continuous, so its image of the product of three capped simplexes is compact and closed. realRankProfile_mem_finiteTest15 uses closedness to pass to the quantization limit.

**Theorem 1.7 (Compression from disjoint finite supports).**

$$\forall A \in \mathit{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{LinearOrder}\left(A\right)], \forall a \in (A \to \mathbb{R}), b \in (A \to \mathbb{R}), c \in (A \to \mathbb{R}),\; \left(\left(\left(\left(\left(\operatorname{IsProbability}\left(a\right) \land \operatorname{IsProbability}\left(b\right)\right) \land \operatorname{IsProbability}\left(c\right)\right) \land \operatorname{Disjoint}\left(\operatorname{weightSupport}\left(a\right), \operatorname{weightSupport}\left(b\right)\right)\right) \land \operatorname{Disjoint}\left(\operatorname{weightSupport}\left(a\right), \operatorname{weightSupport}\left(c\right)\right)\right) \land \operatorname{Disjoint}\left(\operatorname{weightSupport}\left(b\right), \operatorname{weightSupport}\left(c\right)\right)\right) \Rightarrow \operatorname{profile}\left(a, b, c\right) \in \mathit{finiteTest15}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.profile_mem_finiteTest15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sándor Bozóki, László Csató, József Temesi (2026). *Condorcet’s nontransitive dice: A minimal realization of a complete ranking profile*. DOI: [10.48550/arXiv.2611.23308](https://doi.org/10.48550/arXiv.2611.23308). URL: <https://arxiv.org/abs/2611.23308v1>.

*Commentary.*

For three probability weights on an arbitrary finite linear order, pairwise disjoint supports suffice for the profile to pass the test. With two weights fixed, two complementary block sums express two coordinates in terms of the other four. Carathéodory reduces the varying weight to at most five labels in its original support. Compress each role and relabel the union in increasing order. realRankProfile_mem_finiteTest15 applies this result at every quantization scale.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.IsProbability`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.finiteTest15`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.isClosed_finiteTest15`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.profile`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.profile_mem_finiteTest15`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.rankMass`
- Truth anchor: `D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid.weightSupport`
