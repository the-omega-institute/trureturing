# First letters at a fixed inversion number

## Abstract

For k<n, the mean first letter at inversion number k is M(n+1,k)/M(n,k).

Permutations are Equiv.Perm (Fin n), with positions numbered from zero. The existing PSW.word sends a permutation pi to List.ofFn (fun i => (pi i).val + 1), so its entries are the source's one-based letters. D5.S1.Digit.Carry.ListInversions.inv counts strictly inverted pairs of positions. Nat.cast in the formulas below has codomain Q, the rational field. The function List.headD returns its default zero on an empty word; k<n implies n>0.

**Definition 1.1 (Mahonian cardinalities).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{M}\left(n, k\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(((pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{D5.S1.Digit.Carry.ListInversions.inv}\left(\operatorname{PSW.word}\left(pi\right)\right) = k), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.M` (`✓ std3`).

*Citation.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Section 5.2, page 20: “where M(n, k), as above, is the number of permutations w ∈ S_n such that inv(w) = k.” The finite set contains each permutation once and retains exactly inversion number k.

**Definition 1.2 (The conditional mean).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{E}\left(n, k\right) = \frac{\sum_{pi \in \operatorname{Finset.filter}\left(((pi: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto \operatorname{D5.S1.Digit.Carry.ListInversions.inv}\left(\operatorname{PSW.word}\left(pi\right)\right) = k), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)\right))\right)} (\operatorname{Nat.cast}\left(\operatorname{List.headD}\left(\operatorname{PSW.word}\left(pi\right), 0\right)\right): \mathbb{Q})}{(\operatorname{Nat.cast}\left(\operatorname{M}\left(n, k\right)\right): \mathbb{Q})}$$

*Formalization.* `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.E` (`✓ std3`).

*Citation.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Section 5.2, page 20: “Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.” Here mah is inv. Each first letter is cast to Q before summation, and M(n,k) is cast to Q before division. Rational division is total, including when the finite set is empty.

**Definition 1.3 (Kagey's Conjecture 5.1).**

$$claim = (\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; k < n \Rightarrow \operatorname{E}\left(n, k\right) = \frac{(\operatorname{Nat.cast}\left(\operatorname{M}\left(n + 1, k\right)\right): \mathbb{Q})}{(\operatorname{Nat.cast}\left(\operatorname{M}\left(n, k\right)\right): \mathbb{Q})})$$

*Formalization.* `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.claim` (`✓ std3`).

*Citation.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Conjecture 5.1, page 20: “For fixed k and n > k, the expected value of the first letter of a permutation with a given number of inversions satisfies a rational function in n given by E[π(1) | π ∈ S_n, inv(π) = k] = M(n + 1, k)/M(n, k), where M(n, k), as above, is the number of permutations w ∈ S_n such that inv(w) = k.” Both k and n range over natural numbers; k<n is the complete hypothesis.

**Theorem 1.4 (The first-letter expectation identity).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; k < n \Rightarrow \operatorname{E}\left(n, k\right) = \frac{(\operatorname{Nat.cast}\left(\operatorname{M}\left(n + 1, k\right)\right): \mathbb{Q})}{(\operatorname{Nat.cast}\left(\operatorname{M}\left(n, k\right)\right): \mathbb{Q})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2021). *Expected value of letters of permutations with a given number of k-cycles*. DOI: [10.48550/arXiv.2112.05281](https://doi.org/10.48550/arXiv.2112.05281). URL: <https://arxiv.org/abs/2112.05281v1>.

*Commentary.*

Deleting first letter j removes j−1 inversions. Two successive insertions with total inversion contribution t have t+1 choices when t≤k<n. Their count equals the first-letter weight. Thus the natural weighted numerator is M(n+1,k); casting that identity to Q proves the displayed equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.E`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.M`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.result`
- Dependency: [D5/S1/Digit/Carry/ListInversions](../../../S1/Digit/Carry/ListInversions.md)
- Dependency: [D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsWord](../Permanental/PanSkanderaWangAllSplitsWord.md)
