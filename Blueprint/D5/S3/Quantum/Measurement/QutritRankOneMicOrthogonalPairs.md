# A rank-one qutrit MIC with nine orthogonal pairs

## Abstract

Nine positive semidefinite rank-one effects on C^3 sum to the identity and span every Hermitian matrix over the reals. Nine distinct unordered pairs have zero trace product. This refutes Conjecture 1 of DeBrota, Fuchs and Stacey, arXiv:1812.08762v5, which allows at most seven such pairs. The effects have unequal traces.

**Definition 1.1 (Rank-one minimal informational completeness).**

$$\forall E \in \operatorname{Fin}\left(9\right) \to \mathbb{C}^{3\times 3},\; \operatorname{IsRankOneMIC}\left(E\right) \Leftrightarrow ((\forall a \in \operatorname{Fin}\left(9\right),\; \operatorname{PosSemidef}\left(E\left(a\right)\right)) \land ((\sum_{a} E\left(a\right) = 1) \land ((\forall a \in \operatorname{Fin}\left(9\right),\; \operatorname{rank}\left(E\left(a\right)\right) = 1) \land ((\forall a \in \operatorname{Fin}\left(9\right),\; \operatorname{IsHermitian}\left(E\left(a\right)\right)) \land (\forall H \in \mathbb{C}^{3\times 3},\; (\operatorname{IsHermitian}\left(H\right)) \Rightarrow (\exists c \in \operatorname{Fin}\left(9\right) \to \mathbb{R},\; H = \sum_{a} c\left(a\right) \cdot E\left(a\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.IsRankOneMIC` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The source defines a POVM (printed page 1): "Let ℋ_d be a d-dimensional complex Hilbert space, and let {E_i} be a set of positive semidefinite operators on that space which sum to the identity: ∑_(i=1)^N E_i = I." "The set {E_i} is a positive-operator-valued measure (POVM), which is the mathematical representation of a measurement process in quantum theory." It then says (printed pages 1-2): "A POVM is said to be informationally complete (IC) if the operators {E_i} span ℒ(ℋ_d), the space of Hermitian operators on ℋ_d, and an IC POVM is said to be minimal if it contains exactly d² elements." Here d = 3, the index type is Fin 9, and each effect has Matrix.rank = 1. The span is over R: every Hermitian H is a real linear combination of the effects, and the effects themselves are Hermitian. Thus the span is exactly the Hermitian space. There is no condition that the traces are equal.

**Definition 1.2 (Unordered orthogonal pairs).**

$$\forall E \in \operatorname{Fin}\left(9\right) \to \mathbb{C}^{3\times 3},\; \operatorname{orthogonalPairs}\left(E\right) = \{ (a, b) \in \operatorname{Fin}\left(9\right)\times \operatorname{Fin}\left(9\right) \mid (a < b) \land (\operatorname{trace}\left(E\left(a\right) E\left(b\right)\right) = 0) \}$$

*Formalization.* `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.orthogonalPairs` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The paper defines the Gram matrix by "[G]_{ij} := tr E_i E_j" (printed page 2). Its seven-pair example counts distinct unordered pairs. We represent each pair once by (a,b) with a < b in Fin 9; diagonal pairs are excluded. Orthogonality is the complex equality tr(E(a) E(b)) = 0. No real-part test replaces it.

**Definition 1.3 (Conjecture 1).**

$$claim \Leftrightarrow (\forall E \in \operatorname{Fin}\left(9\right) \to \mathbb{C}^{3\times 3},\; (\operatorname{IsRankOneMIC}\left(E\right)) \Rightarrow (\operatorname{card}\left(\operatorname{orthogonalPairs}\left(E\right)\right) \le 7))$$

*Formalization.* `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.claim` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

"A rank-1 MIC in dimension 3 can have no more than 7 pairs of orthogonal elements." (Conjecture 1, printed page 6, arXiv:1812.08762v5.) E ranges over all families of nine complex 3 by 3 matrices satisfying IsRankOneMIC. The pairs are counted once by increasing indices. The preceding example (printed page 5) says "When multiplied by 1/3, the following is a rank-1 unbiased MIC in dimension 3 with 7 orthogonal pairs." The conjecture itself says rank-1 MIC and imposes no unbiasedness condition.

**Theorem 1.4 (Nine pairs refute the seven-pair bound).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result` (`✓ std3`). ∎

*Resolves.* `Problems/debrota-2020-rank-one-mic-seven-orthogonal-pairs-refutation` (refuted) by `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"debrota-2020-rank-one-mic-seven-orthogonal-pairs-refutation","declaration_gid":"D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

Let v = [(1,i,-1), (1,-1,1+i), (1-i,0,-1), (1,-1+i,1+i), (0,1,i), (-1-i,i,1), (1,1,1), (1,i,-1-i), (1,-i,0)] and k = [3,2,2,4,3,3,9,7,11], with indices 0 through 8. The effects E(a) = (k(a)/46) v(a) v(a)^* are positive semidefinite; each outer product has rank at most one and a nonzero diagonal entry establishes rank at least one. Their sum is I. For x = [Re H00, Re H11, Re H22, Re H01, Im H01, Re H02, Im H02, Re H12, Im H12], define c(a) = (Jx)(a)/k(a), where J is the integer matrix 46 times the inverse of the coordinate matrix of the outer products. Expanding gives H = ∑_a c(a) E(a) for every Hermitian H. The nine pairs (0,1), (0,8), (1,2), (2,3), (3,4), (4,5), (5,6), (6,7), (7,8) have zero trace product. Their cardinality is nine, so the total number is at least nine and cannot be at most seven. The traces are 9/46, 4/23, 3/23, 10/23, 3/23, 6/23, 27/46, 14/23, 11/23; this example is biased.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.IsRankOneMIC`
- Truth anchor: `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.orthogonalPairs`
- Truth anchor: `D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs.result`
