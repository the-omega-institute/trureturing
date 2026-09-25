# Oh and Scrimshaw's two-shifted q-Motzkin conjecture is false as printed

## Abstract

At n = 3 the two-shifted Hankel determinant of Cigler's q-Motzkin numbers takes the value 3 at q = 1, while the printed factor f_3 takes the value 2, so no power of q times f_3 equals the determinant.

**Definition 1.1 (Cigler's q-Motzkin numbers).**

$$(\operatorname{qMotzkin}\left(q, 0\right) = 1) \land (\forall n \in \mathbb{N},\; \operatorname{qMotzkin}\left(q, n + 1\right) = \operatorname{qMotzkin}\left(q, n\right) + \sum_{k \in \operatorname{Fin}\left(n\right)} q^{k + 1} \cdot \operatorname{qMotzkin}\left(q, k\right) \cdot \operatorname{qMotzkin}\left(q, n - k - 1\right))$$

*Formalization.* `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.qMotzkin` (`✓ std3`).

*Citation.* Se-jin Oh, Travis Scrimshaw (2018). *Identities from representation theory*. DOI: [10.48550/arXiv.1805.00113](https://doi.org/10.48550/arXiv.1805.00113). URL: <https://arxiv.org/abs/1805.00113v1>.

*Commentary.*

The recursion of the source over any commutative ring with parameter q: M(0) = 1 and M(n + 1) = M(n) + sum over k < n of q^(k+1) M(k) M(n - k - 1). The conjecture uses the polynomial ring Z[q] with q the variable.

**Definition 1.2 (The printed factor).**

$$\forall n \in \mathbb{N},\; \operatorname{fPrinted}\left(q, n\right) = \operatorname{ite}\left(\operatorname{NatMod}\left(n, 3\right) = 0, \sum_{k \in \{k \in \operatorname{Finset.Icc}\left(1, n\right) \mid \operatorname{NatMod}\left(k, 3\right) \ne 1\}} q^{k}, (q + 1) \cdot \sum_{k \in \operatorname{Finset.range}\left(\operatorname{NatDiv}\left(n, 3\right) + 1\right)} q^{3 \cdot k}\right)$$

*Formalization.* `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.fPrinted` (`✓ std3`).

*Citation.* Se-jin Oh, Travis Scrimshaw (2018). *Identities from representation theory*. DOI: [10.48550/arXiv.1805.00113](https://doi.org/10.48550/arXiv.1805.00113). URL: <https://arxiv.org/abs/1805.00113v1>.

*Commentary.*

For n divisible by three the source sums q^k over 1 <= k <= n with k not congruent to 1 modulo 3; otherwise it multiplies q + 1 by the sum of q^(3k) over k <= floor(n/3). NatMod and NatDiv are the natural remainder and quotient.

**Definition 1.3 (The two-shifted Hankel determinant).**

$$\forall n \in \mathbb{N},\; \operatorname{hankelTwoShifted}\left(q, n\right) = \operatorname{det}\left([\operatorname{qMotzkin}\left(q, i + j + 2\right)]_{i, j \in \operatorname{Fin}\left(n\right)}\right)$$

*Formalization.* `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.hankelTwoShifted` (`✓ std3`).

*Citation.* Se-jin Oh, Travis Scrimshaw (2018). *Identities from representation theory*. DOI: [10.48550/arXiv.1805.00113](https://doi.org/10.48550/arXiv.1805.00113). URL: <https://arxiv.org/abs/1805.00113v1>.

*Commentary.*

The determinant of the n x n matrix with entries M(i + j + 2) for 0 <= i, j < n.

**Definition 1.4 (The printed conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\exists c \in \mathbb{N},\; \operatorname{hankelTwoShifted}\left(X, n\right) = X^{c} \cdot \operatorname{fPrinted}\left(X, n\right)))$$

*Formalization.* `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.claim` (`✓ std3`).

*Citation.* Se-jin Oh, Travis Scrimshaw (2018). *Identities from representation theory*. DOI: [10.48550/arXiv.1805.00113](https://doi.org/10.48550/arXiv.1805.00113). URL: <https://arxiv.org/abs/1805.00113v1>.

*Commentary.*

For every n >= 1 some natural power of q times f_n equals the determinant in Z[q]. Only the first of the two conjectures that share the label conj:factored_motzkin_2shifted is stated.

**Theorem 1.5 (The counterexample n = 3).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oh-scrimshaw-2018-two-shifted-q-motzkin-hankel-refutation` (refuted) by `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oh-scrimshaw-2018-two-shifted-q-motzkin-hankel-refutation","declaration_gid":"D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Se-jin Oh, Travis Scrimshaw (2018). *Identities from representation theory*. DOI: [10.48550/arXiv.1805.00113](https://doi.org/10.48550/arXiv.1805.00113). URL: <https://arxiv.org/abs/1805.00113v1>.

*Commentary.*

Evaluation at q = 1 is a ring homomorphism from Z[q] to Z, so it commutes with the determinant and with the recursion. At q = 1 the recursion gives the Motzkin numbers 1, 1, 2, 4, 9, 21, 51, and the determinant becomes det[[2, 4, 9], [4, 9, 21], [9, 21, 51]] = 3. The printed side becomes 1^c f_3(1), and f_3 = q^2 + q^3 gives 2. So the identity fails at n = 3 for every c.

## References

- Truth anchor: `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.claim`
- Truth anchor: `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.fPrinted`
- Truth anchor: `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.hankelTwoShifted`
- Truth anchor: `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.qMotzkin`
- Truth anchor: `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.result`
