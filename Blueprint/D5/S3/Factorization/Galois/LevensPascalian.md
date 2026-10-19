# A square-discriminant obstruction for the Pascalian polynomial of degree 49

## Abstract

The square discriminant of the degree twenty-four binomial truncation refutes the odd-index Galois-group conjecture at n = 49.

**Definition 1.1 (The Pascalian polynomial).**

$$\forall (n: \mathbb{N}), (\operatorname{D5.S3.Factorization.Galois.LevensPascalian.P}\left(n\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} (\operatorname{Polynomial.C}\left((\operatorname{Nat.choose}\left(n, \operatorname{Nat.div}\left(n - k, 2\right)\right): \mathbb{Q})\right) \cdot \operatorname{Polynomial.X}^{n - k}))$$

*Formalization.* `D5/S3/Factorization/Galois/LevensPascalian.P` (`✓ std3`).

*Citation.* Owen Levens (2025). *Polynomials Arising from Sorted Binomial Coefficients*. DOI: [10.48550/arXiv.2511.03082](https://doi.org/10.48550/arXiv.2511.03082). URL: <https://arxiv.org/abs/2511.03082v1>.

*Commentary.*

Section 1, printed page 1: “let ⟨n k⟩ = C(n, ⌊(n−k)/2⌋) for 0 ≤ k ≤ n, call the ⟨n k⟩ triangle the Pascalian numbers, and let the nth Pascalian polynomial be P_n(z) = Σ_{k=0}^{n} ⟨n k⟩ z^{n−k}.” The coefficient binomial is Nat.choose, cast into ℚ and then embedded by Polynomial.C. The index k ranges from zero through n; subtraction and Nat.div are operations on ℕ, so Nat.div (n − k) 2 is the floor in this range.

**Definition 1.2 (Sign change on the signed letters).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.Factorization.Galois.LevensPascalian.signFlip}\left(m\right) = \operatorname{Equiv.prodCongr}\left(\operatorname{Equiv.refl}\left(\operatorname{Fin}\left(m\right)\right), \operatorname{Equiv.swap}\left(\operatorname{false}, \operatorname{true}\right)\right))$$

*Formalization.* `D5/S3/Factorization/Galois/LevensPascalian.signFlip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two Boolean values represent the two signs. Equiv.prodCongr fixes the Fin m coordinate and swaps false with true.

**Definition 1.3 (The group of signed permutations).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.Factorization.Galois.LevensPascalian.hyperoctahedral}\left(m\right) = \operatorname{Subgroup.centralizer}\left(\left\{\operatorname{D5.S3.Factorization.Galois.LevensPascalian.signFlip}\left(m\right)\right\}\right))$$

*Formalization.* `D5/S3/Factorization/Galois/LevensPascalian.hyperoctahedral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mth hyperoctahedral group is represented as the subgroup of permutations of Fin m × Bool commuting with signFlip m. This centralizer has order 2^m m!.

**Definition 1.4 (Levens Conjecture 6.4, odd-index clause).**

$$\operatorname{D5.S3.Factorization.Galois.LevensPascalian.claim} = (\forall (m: \mathbb{N}), ((1 \le m) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{MulEquiv}\left(\operatorname{Polynomial.Gal}\left(\operatorname{D5.S3.Factorization.Galois.LevensPascalian.P}\left(2 \cdot m + 1\right)\right), \operatorname{D5.S3.Factorization.Galois.LevensPascalian.hyperoctahedral}\left(m\right)\right)\right))))$$

*Formalization.* `D5/S3/Factorization/Galois/LevensPascalian.claim` (`✓ std3`).

*Citation.* Owen Levens (2025). *Polynomials Arising from Sorted Binomial Coefficients*. DOI: [10.48550/arXiv.2511.03082](https://doi.org/10.48550/arXiv.2511.03082). URL: <https://arxiv.org/abs/2511.03082v1>.

*Commentary.*

Conjecture 6.4, printed page 20: “P_n(z) has full Galois group for even n. For n = 2m + 1, the Galois group of P_n(z) is the mth hyperoctahedral group.” The displayed proposition is the second sentence, for natural m ≥ 1. Polynomial.Gal is the automorphism group of the splitting field over ℚ. Being the indicated group means the existence of an abstract multiplicative equivalence, expressed by Nonempty; disproving this also excludes an isomorphism as permutation groups.

**Theorem 1.5 (The odd-index assertion is false).**

$$\neg (\forall (m: \mathbb{N}), ((1 \le m) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{MulEquiv}\left(\operatorname{Polynomial.Gal}\left(\operatorname{D5.S3.Factorization.Galois.LevensPascalian.P}\left(2 \cdot m + 1\right)\right), \operatorname{D5.S3.Factorization.Galois.LevensPascalian.hyperoctahedral}\left(m\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/LevensPascalian.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Owen Levens (2025). *Polynomials Arising from Sorted Binomial Coefficients*. DOI: [10.48550/arXiv.2511.03082](https://doi.org/10.48550/arXiv.2511.03082). URL: <https://arxiv.org/abs/2511.03082v1>.

*Commentary.*

At m = 24, put c = 63205303218876 = Nat.choose 49 24 and q(X) = ∑ j ∈ Finset.range 25, Polynomial.C ((Nat.choose 49 j : ℕ) : ℚ) * X^j. Then P 49 = (1 + X) * q.comp (X^2), and (1 + X) * q.derivative − Polynomial.C 49 * q = −Polynomial.C (25*c) * X^24. Resultant identities give q.discr = (7 * 5^23 * c^11)^2. These polynomial and rational identities are checked inside the proof.

The Vandermonde determinant of the twenty-four distinct roots of q is rational and nonzero. Every field automorphism fixes it, so its permutation of those roots has sign one. The roots of P 49 are −1 and the signed square roots of the roots of q. Encoding an automorphism by its twenty-four signs and its even permutation is injective. Consequently the Galois group has order at most 2^24 * |alternatingGroup (Fin 24)|, strictly less than the hyperoctahedral order 2^24 * 24!.

This excludes the abstract group isomorphism at n = 49. It does not determine the exact Galois group. The even-index sentence, Conjecture 6.3, and a classification of the other odd indices remain separate questions. The square-discriminant formula is classical; its general form appears in Filaseta–Moy, Lemma 3, as recorded with the source reference.

## References

- Truth anchor: `D5/S3/Factorization/Galois/LevensPascalian.P`
- Truth anchor: `D5/S3/Factorization/Galois/LevensPascalian.claim`
- Truth anchor: `D5/S3/Factorization/Galois/LevensPascalian.hyperoctahedral`
- Truth anchor: `D5/S3/Factorization/Galois/LevensPascalian.result`
- Truth anchor: `D5/S3/Factorization/Galois/LevensPascalian.signFlip`
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../Zeros/Convolution/PerfectMatchingCount.md)
