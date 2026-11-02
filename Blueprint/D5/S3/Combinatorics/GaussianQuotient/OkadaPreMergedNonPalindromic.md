# Almost palindromicity of pre-merged Gaussian determinants

## Abstract

Almost strictly pre-fitting tuples of width at least three give pre-merged Gaussian determinants that are not almost palindromic.

**Definition 1.1 (A palindrome after zero coefficients are omitted).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{Z}\right)), ((\operatorname{IsAlmostPalindromic}\left(f\right)) \Leftrightarrow (\operatorname{List.Palindrome}\left(\operatorname{List.map}\left((\operatorname{DFunLike.coe}\left(\operatorname{Polynomial.coeff}\left(f\right)\right): \mathbb{N} \to \mathbb{Z}), \operatorname{Finset.sort}\left(\operatorname{Polynomial.support}\left(f\right), \lambda (x1: \mathbb{N}) \mapsto (\lambda (x2: \mathbb{N}) \mapsto (x1 \le x2))\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.IsAlmostPalindromic` (`✓ std3`).

*Citation.* Okada, So (2020). *Merged-log-concavity of rational functions, almost strictly unimodal sequences, and phase transitions of ideal boson-fermion gases*. DOI: [10.48550/arXiv.2003.02112](https://doi.org/10.48550/arXiv.2003.02112). URL: <https://arxiv.org/abs/2003.02112v2>.

*Commentary.*

Sort the finite support of the integer polynomial f by increasing natural degree, and list its coefficients in that order. IsAlmostPalindromic applies List.Palindrome to this list. By List.Palindrome.iff_reverse_eq, this is equivalent to equality with its reverse. The coercion DFunLike.coe turns the finitely supported coefficient map into a function from natural degrees to integers. The empty list makes the zero polynomial almost palindromic. This is the integer-coefficient form of the definition for rational polynomials in arXiv:2003.02112v2, phases.tex, lines 8503–8512.

**Definition 1.2 (The pre-merged difference of Gaussian products).**

$$\forall (\mu: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(\mu\right) \to \mathbb{N}), (\forall (b: \operatorname{Fin}\left(\mu\right) \to \mathbb{N}), ((\operatorname{preMerged}\left(a, b\right): \operatorname{Polynomial}\left(\mathbb{Z}\right)) = (\prod_{(i: \operatorname{Fin}\left(\mu\right))} (\operatorname{D5.S3.Combinatorics.CylindricPartition.LiUncuDefs.gauss}\left(b\left(i\right), a\left(i\right)\right))) - (\prod_{(i: \operatorname{Fin}\left(\mu\right))} (\operatorname{D5.S3.Combinatorics.CylindricPartition.LiUncuDefs.gauss}\left(b\left(i\right), a\left(\operatorname{Fin.rev}\left(i\right)\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.preMerged` (`✓ std3`).

*Citation.* Okada, So (2020). *Merged-log-concavity of rational functions, almost strictly unimodal sequences, and phase transitions of ideal boson-fermion gases*. DOI: [10.48550/arXiv.2003.02112](https://doi.org/10.48550/arXiv.2003.02112). URL: <https://arxiv.org/abs/2003.02112v2>.

*Commentary.*

For natural tuples a and b of length μ, subtract the Gaussian product with a in reverse order from the product with a in its original order. Fin.rev sends index i to μ − 1 − i; all indices begin at zero. The Gaussian polynomial gauss has integer coefficients. The definition itself allows every μ and every pair of natural tuples, without monotonicity assumptions. It specializes the source's pre-merged determinant to unit weights, unit base shifts, zero degree shift, and a common indeterminate. The base shift factors are then one. See phases.tex, lines 755–762, 3508–3519, 5942–5958, and 6005–6048.

**Definition 1.3 (The assertion for every width at least three).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (\mu: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(\mu\right) \to \mathbb{N}), (\forall (b: \operatorname{Fin}\left(\mu\right) \to \mathbb{N}), ((3 \le \mu) \Rightarrow ((\operatorname{StrictMono}\left(a\right)) \Rightarrow ((\operatorname{StrictMono}\left(b\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(\mu\right)), (\forall (j: \operatorname{Fin}\left(\mu\right)), (a\left(i\right) \le b\left(j\right)))) \Rightarrow (\neg (\operatorname{IsAlmostPalindromic}\left(\operatorname{preMerged}\left(a, b\right)\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.claim` (`✓ std3`).

*Citation.* Okada, So (2020). *Merged-log-concavity of rational functions, almost strictly unimodal sequences, and phase transitions of ideal boson-fermion gases*. DOI: [10.48550/arXiv.2003.02112](https://doi.org/10.48550/arXiv.2003.02112). URL: <https://arxiv.org/abs/2003.02112v2>.

*Commentary.*

For μ at least three, a and b are strictly increasing natural tuples, and every entry of a is at most every entry of b. The latter condition is equivalent, for these tuples, to the last entry of a being at most the first entry of b. These are precisely the almost strictly pre-fitting tuples of phases.tex, lines 8337–8346. The proposition is the unit-parameter conjecture on non-almost-palindromicity in lines 8770–8779, with the Gaussian difference regarded as an integer polynomial.

**Theorem 1.4 (The second and penultimate coefficients disagree).**

$$\forall (\mu: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(\mu\right) \to \mathbb{N}), (\forall (b: \operatorname{Fin}\left(\mu\right) \to \mathbb{N}), ((3 \le \mu) \Rightarrow ((\operatorname{StrictMono}\left(a\right)) \Rightarrow ((\operatorname{StrictMono}\left(b\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(\mu\right)), (\forall (j: \operatorname{Fin}\left(\mu\right)), (a\left(i\right) \le b\left(j\right)))) \Rightarrow (\neg (\operatorname{IsAlmostPalindromic}\left(\operatorname{preMerged}\left(a, b\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.result` (`✓ std3`). ∎

*Resolves.* `Problems/okada-2020-premerged-determinant-nonpalindromic` (proved) by `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"okada-2020-premerged-determinant-nonpalindromic","declaration_gid":"D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Okada, So (2020). *Merged-log-concavity of rational functions, almost strictly unimodal sequences, and phase transitions of ideal boson-fermion gases*. DOI: [10.48550/arXiv.2003.02112](https://doi.org/10.48550/arXiv.2003.02112). URL: <https://arxiv.org/abs/2003.02112v2>.

*Commentary.*

Fix μ, a and b satisfying the hypotheses. Gaussian symmetry gives diagonal value one. The Gaussian recurrence gives constant coefficient one whenever the lower index does not exceed the upper index. Its linear coefficient is one when the lower index is positive and strictly smaller than the upper index.

For a natural n, write (X)ₙ for the product of 1 − Xʰ over 1 ≤ h ≤ n. Induction using the Gaussian hook identity gives gauss(n,k) (X)ₖ (X)ₙ₋ₖ = (X)ₙ for k ≤ n. Let t = b(0) − a(μ − 1). Strict increase, the cross inequalities and μ ≥ 3 give b(i) − a(i) ≥ t + 2 for every i. For reversed a, the difference at index zero is t, and every other difference is at least t + 2. All these differences are natural subtraction.

Write a0 and b0 for the original and reversed Gaussian products, respectively. Multiplying the factorial identity over the indices, reindexing the a-factorials by Equiv.prod_comp with Fin.revPerm, and cancelling gives a0 ∏ᵢ (X)ᵦ₍ᵢ₎₋ₐ₍ᵢ₎ = b0 ∏ᵢ (X)ᵦ₍ᵢ₎₋ₐ₍Fin.rev i₎. The cancelled polynomial is nonzero because its constant coefficient is one.

Work in the quotient of ℤ[X] by the ideal generated by X^(t + 3). There X is nilpotent, each (X)ₙ is a unit, and its image is independent of n once n ≥ t + 2. The original difference-factorials therefore have product (X)ₜ₊₂^μ, while the reversed ones have product (X)ₜ (X)ₜ₊₂^(μ − 1). Since (X)ₜ₊₂ = (X)ₜ (1 − X^(t + 1))(1 − X^(t + 2)), unit cancellation gives b0 = a0 (1 − X^(t + 1))(1 − X^(t + 2)) in this quotient.

Put p = preMerged(a,b), r = t + 1, and let the natural number c be μ if a(0) > 0 and μ − 1 otherwise. The constant coefficient of a0 is one. The coefficient of degree one in a product of factors with constant coefficient one is the sum of their linear coefficients: apply the finite-product derivative identity derivative_prod_finset and take the constant coefficient. Thus the linear coefficient of a0 is (c : ℤ). If a(0) = 0, precisely the first factor contributes zero instead of one. The quotient identity now gives p.coeff(r) = 1, p.coeff(r + 1) = (c : ℤ) + 1, and p.coeff(n) = 0 for every n < r.

Next, induction on the Gaussian recurrence proves that gauss(n,k) is monic, has natural degree k(n − k), and equals its polynomial reverse when k ≤ n. The dual Gaussian recurrence identifies the reflected sum in the induction step. The library's monic-product and degree identities, and reverse_mul_of_domain via Finset.prod_induction, extend these properties to products. Thus a0 has natural degree d = ∑ᵢ a(i)(b(i) − a(i)), and b0 has natural degree e = ∑ᵢ a(Fin.rev i)(b(i) − a(Fin.rev i)).

To compare these degrees, cast every tuple entry from ℕ to ℤ. For each i, the product of the integer differences ((a(i) : ℤ) − (a(Fin.rev i) : ℤ)) and ((b(i) : ℤ) − (b(Fin.rev i) : ℤ)) is nonnegative: the two cast tuples are monotone, so the library's monovariation inequality applies. Summing and reindexing by Equiv.sum_comp with Fin.revPerm gives 2((d : ℤ) − (e : ℤ)). At index zero both differences are at most −2, so this sum is at least four. Consequently e + 2 ≤ d in ℕ.

The last entry a(μ − 1) is at least two, and b(μ − 1) − a(μ − 1) is at least t + 2. Its contribution to d gives d ≥ t + 4. The leading coefficient of a0 is one; reversal equates its coefficient at d − 1 with its linear coefficient (c : ℤ). Since e + 2 ≤ d, subtracting b0 changes neither coefficient. Hence p has natural degree d, with coefficients one at d and (c : ℤ) at d − 1.

Finally c is positive and r + 1 < d − 1. In the increasing list of degrees in the support of p, the first two entries must be r and r + 1, and the last two must be d − 1 and d. Indeed, the coefficients at these four degrees are nonzero, none occur below r or above d, and the pairs are adjacent natural degrees. If the coefficient list satisfied List.Palindrome, List.Palindrome.iff_reverse_eq would identify its reverse with itself. Comparing index one with List.getElem?_reverse would then equate its second entry (c : ℤ) + 1 with its penultimate entry (c : ℤ). This is impossible, so p is not almost palindromic.

## References

- Truth anchor: `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.IsAlmostPalindromic`
- Truth anchor: `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.claim`
- Truth anchor: `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.preMerged`
- Truth anchor: `D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic.result`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian](../CylindricPartition/LiUncuGaussian.md)
