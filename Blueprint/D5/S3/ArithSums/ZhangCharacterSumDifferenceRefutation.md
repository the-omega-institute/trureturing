# A Constant-One Difference of Polynomial Character Sums

## Abstract

Two quadratic-polynomial Legendre sums differ by one for every odd prime.

The Legendre symbol notation and the range from one through p-1 are those of identity (2). The paper's preceding corollary quantifies over odd primes.

**Definition 1.1 (The polynomial Legendre character sum).**

$$\forall p \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \Rightarrow (\forall f \in \mathbb{Z}[X],\; \operatorname{characterSum}\left(p, f\right) = \sum_{x = 1}^{p - 1} (\frac{f\left((x: \mathbb{Z})\right)}{p}))$$

*Formalization.* `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.characterSum` (`✓ std3`).

*Citation.* Wenpeng Zhang (2025). *Some interesting number theory problems*. DOI: [10.48550/arXiv.2506.17235](https://doi.org/10.48550/arXiv.2506.17235). URL: <https://arxiv.org/abs/2506.17235v1>.

*Commentary.*

For a prime p and an integer-coefficient polynomial f, this is the sum of the Legendre symbols of f(x) over the integers from one through p-1.

**Definition 1.2 (Fundamental difference on the summation domain).**

$$\forall p \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \Rightarrow (\forall f \in \mathbb{Z}[X], g \in \mathbb{Z}[X],\; (\operatorname{FundamentallyDifferent}\left(p, f, g\right)) \Leftrightarrow (\exists x \in \mathbb{N},\; ((1 \le x) \land (x < p)) \land ((\frac{f\left((x: \mathbb{Z})\right)}{p}) \ne (\frac{g\left((x: \mathbb{Z})\right)}{p}))))$$

*Formalization.* `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.FundamentallyDifferent` (`✓ std3`).

*Citation.* Wenpeng Zhang (2025). *Some interesting number theory problems*. DOI: [10.48550/arXiv.2506.17235](https://doi.org/10.48550/arXiv.2506.17235). URL: <https://arxiv.org/abs/2506.17235v1>.

*Commentary.*

The two symbol-valued functions are different when some x in the same finite summation domain gives unequal values. This is equivalent to inequality of those functions on that domain.

**Definition 1.3 (The constant-value assertion in Question (D)).**

$$(claim) \Leftrightarrow (\forall f \in \mathbb{Z}[X], g \in \mathbb{Z}[X], c \in \mathbb{Z},\; (\forall p \in \mathbb{N},\; ((\operatorname{Prime}\left(p\right)) \land (p \ne 2)) \Rightarrow ((\operatorname{FundamentallyDifferent}\left(p, f, g\right)) \land (\operatorname{characterSum}\left(p, f\right) - \operatorname{characterSum}\left(p, g\right) = c))) \Rightarrow ((c = 0) \lor (c = 2)))$$

*Formalization.* `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.claim` (`✓ std3`).

*Citation.* Wenpeng Zhang (2025). *Some interesting number theory problems*. DOI: [10.48550/arXiv.2506.17235](https://doi.org/10.48550/arXiv.2506.17235). URL: <https://arxiv.org/abs/2506.17235v1>.

*Commentary.*

Question (B) asks: "Whether there are infinitely many pairs of fundamentally different integer coefficients polynomials f(x) and g(x) (That is, (f(x)/p) ≠ (g(x)/p)) such that Σ_{x=1}^{p−1} (f(x)/p) − Σ_{x=1}^{p−1} (g(x)/p) = c, (2) where c is a fixed constant." Question (D) asks: "Whether the values of c can only be 0 or 2?" Identity (2) does not print an explicit universal binder for p. Here one integer c is bound outside the universal odd-prime condition, following the preceding corollary. Thus the same c is the difference for every odd prime, and the two symbol functions differ at every such prime.

**Theorem 1.4 (A constant-one counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-character-sum-difference-question-d-refutation` (refuted) by `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-character-sum-difference-question-d-refutation","declaration_gid":"D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Wenpeng Zhang (2025). *Some interesting number theory problems*. DOI: [10.48550/arXiv.2506.17235](https://doi.org/10.48550/arXiv.2506.17235). URL: <https://arxiv.org/abs/2506.17235v1>.

*Commentary.*

Take f(X)=X^2 and g(X)=(X+1)^2. For every odd prime p, the first sum is p-1. The second is p-2 because its final term, at x=p-1, is zero and every earlier term is one. At that same endpoint the first symbol is one, so the functions differ. Their sum difference is the fixed integer c=1, which is neither zero nor two.

## References

- Truth anchor: `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.FundamentallyDifferent`
- Truth anchor: `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.characterSum`
- Truth anchor: `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.claim`
- Truth anchor: `D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.result`
