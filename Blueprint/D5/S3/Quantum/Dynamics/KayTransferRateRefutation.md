# An eight-level perfect state transfer spectrum fulfils Kay's rate condition with M = 4

## Abstract

Kay's review of perfect state transfer (arXiv:0903.4274v3, subsection Transfer Rate) conjectures that no set of eigenvalues fulfilling the perfect state transfer condition can make all the sums R_k, k = 0, ..., M - 1, of its rate lemma equal for an integer M > 2, and states that it has a proof only for M > N/2. The conjecture is false: for the eight eigenvalues 0, 31, 46, 65, 88, 107, 122, 153 with transfer time pi and M = 4 = N/2, all four sums equal 194/38984495395755.

**Definition 1.1 (The perfect state transfer condition).**

$$\forall N \in \mathbb{N},\; \forall lam \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; \operatorname{SpectrumCondition}\left(lam, t\right) \Leftrightarrow (0 < t \land \left(\exists m \in \mathbb{N} \to \mathbb{N},\; \forall n \in \mathbb{N},\; (n + 1 < N) \Rightarrow (0 < m\left(n\right) \land lam\left(n + 1\right) - lam\left(n\right) = \frac{(2 \cdot m\left(n\right) + 1) \cdot \pi}{t})\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.SpectrumCondition` (`✓ std3`).

*Citation.* Alastair Kay (2010). *A Review of Perfect State Transfer and its Application as a Constructive Tool*. DOI: [10.1142/S0219749910006514](https://doi.org/10.1142/S0219749910006514). URL: <https://arxiv.org/abs/0903.4274v3>.

*Commentary.*

The source orders the eigenvalues of the chain as lambda_1 < ... < lambda_N and states the condition "lambda_n - lambda_{n-1} = (2 m_n + 1) pi / t_0 where t_0 is the state transfer time, and m_n is a positive integer (which can vary with n)." Here the levels are lam(0), ..., lam(N - 1), the transfer time is t, and m(n) is the multiplier of the gap between the levels n and n + 1. The gaps are positive, so the levels are strictly increasing.

**Definition 1.2 (The derivative of the characteristic product).**

$$\forall N \in \mathbb{N},\; \forall lam \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall n \in \operatorname{Fin}\left(N\right),\; \operatorname{derivativeAt}\left(lam, n\right) = \prod_{j \in \operatorname{Fin}\left(N\right), j \ne n} (lam\left(n\right) - lam\left(j\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.derivativeAt` (`✓ std3`).

*Citation.* Alastair Kay (2010). *A Review of Perfect State Transfer and its Application as a Constructive Tool*. DOI: [10.1142/S0219749910006514](https://doi.org/10.1142/S0219749910006514). URL: <https://arxiv.org/abs/0903.4274v3>.

*Commentary.*

The source writes "B'(lambda_n) = prod_{m = 1, m != n}^N (lambda_n - lambda_m), which is the derivative of the function B(lambda) = prod_{m=1}^N (lambda - lambda_m)". The product runs over the levels j different from n.

**Definition 1.3 (Residue classes of the levels).**

$$\forall N \in \mathbb{N},\; \forall lam \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; \forall M \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall n \in \operatorname{Fin}\left(N\right),\; \operatorname{InClass}\left(lam, t, M, k, n\right) \Leftrightarrow (\exists z \in \mathbb{Z},\; \frac{t}{\pi} \cdot (lam\left(n\right) - lam\left(0\right)) = z \land z \bmod M = k)$$

*Formalization.* `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.InClass` (`✓ std3`).

*Citation.* Alastair Kay (2010). *A Review of Perfect State Transfer and its Application as a Constructive Tool*. DOI: [10.1142/S0219749910006514](https://doi.org/10.1142/S0219749910006514). URL: <https://arxiv.org/abs/0903.4274v3>.

*Commentary.*

The sum R_k of the source "is restricted to those terms satisfying the condition (t_0 / pi)(lambda_n - lambda_1) mod M = k". The level n lies in the class k modulo M when the real number (t / pi)(lam(n) - lam(0)) is an integer z with z mod M = k. Under the perfect state transfer condition this number is the sum of the odd integers 2 m(i) + 1 over the gaps i below n.

**Definition 1.4 (The sums of the rate lemma).**

$$\forall N \in \mathbb{N},\; \forall lam \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; \forall M \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{rateSum}\left(lam, t, M, k\right) = \sum_{n \in \operatorname{Fin}\left(N\right), \operatorname{InClass}\left(lam, t, M, k, n\right)} \frac{(-1)^{\operatorname{val}\left(n\right) + 1}}{\operatorname{derivativeAt}\left(lam, n\right)}$$

*Formalization.* `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.rateSum` (`✓ std3`).

*Citation.* Alastair Kay (2010). *A Review of Perfect State Transfer and its Application as a Constructive Tool*. DOI: [10.1142/S0219749910006514](https://doi.org/10.1142/S0219749910006514). URL: <https://arxiv.org/abs/0903.4274v3>.

*Commentary.*

The source defines "R_k = sum_{n=1}^N (-1)^n / B'(lambda_n)", the sum being restricted to the levels of the residue class k modulo M. The index n of the source starts at one, so the level with the index n in Fin(N) carries the sign (-1)^(val(n) + 1), where val(n) is its position counted from zero.

**Definition 1.5 (The condition of the rate lemma).**

$$\forall N \in \mathbb{N},\; \forall lam \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; \forall M \in \mathbb{N},\; \operatorname{RateCondition}\left(lam, t, M\right) \Leftrightarrow (\forall k \in \mathbb{N},\; (k < M) \Rightarrow (\forall l \in \mathbb{N},\; (l < M) \Rightarrow (\operatorname{rateSum}\left(lam, t, M, k\right) = \operatorname{rateSum}\left(lam, t, M, l\right))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.RateCondition` (`✓ std3`).

*Citation.* Alastair Kay (2010). *A Review of Perfect State Transfer and its Application as a Constructive Tool*. DOI: [10.1142/S0219749910006514](https://doi.org/10.1142/S0219749910006514). URL: <https://arxiv.org/abs/0903.4274v3>.

*Commentary.*

The lemma of the source states that, for a set of eigenvalues fulfilling the perfect state transfer condition, "a necessary and sufficient condition to perfectly achieve the rate M / 2 t_0 for integer M is that all the R_k for k = 0 ... M - 1 should be equal".

**Definition 1.6 (The transfer-rate conjecture).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; (0 < N) \Rightarrow (\forall lam \in \operatorname{Fin}\left(N\right) \to \mathbb{R},\; \forall t \in \mathbb{R},\; (\operatorname{SpectrumCondition}\left(lam, t\right)) \Rightarrow (\forall M \in \mathbb{N},\; (2 < M) \Rightarrow (\neg \operatorname{RateCondition}\left(lam, t, M\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.claim` (`✓ std3`).

*Citation.* Alastair Kay (2010). *A Review of Perfect State Transfer and its Application as a Constructive Tool*. DOI: [10.1142/S0219749910006514](https://doi.org/10.1142/S0219749910006514). URL: <https://arxiv.org/abs/0903.4274v3>.

*Commentary.*

The source states: "We conjecture that it is impossible to fulfill the condition of Lemma 6 for any M > 2, although we only have a proof for M > N/2." The statement quantifies over every number N >= 1 of levels, every set of levels with a transfer time fulfilling the perfect state transfer condition, and every integer M > 2. The empty set of levels is excluded because all its sums are empty and therefore equal.

**Theorem 1.7 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kay-2010-transfer-rate-refutation` (refuted) by `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kay-2010-transfer-rate-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alastair Kay (2010). *A Review of Perfect State Transfer and its Application as a Constructive Tool*. DOI: [10.1142/S0219749910006514](https://doi.org/10.1142/S0219749910006514). URL: <https://arxiv.org/abs/0903.4274v3>.

*Commentary.*

Take N = 8, the levels 0, 31, 46, 65, 88, 107, 122, 153 and the transfer time pi. The gaps are 31, 15, 19, 23, 19, 15, 31, that is 2 m + 1 with m = 15, 7, 9, 11, 9, 7, 15, so the perfect state transfer condition holds. The derivatives B'(lambda_n) are -16291106900640, 760363989840, -273136152240, 203460697440, -203460697440, 273136152240, -760363989840, 16291106900640. For M = 4 the residues of the levels are 0, 3, 2, 1, 0, 3, 2, 1, so the classes are {0, 88}, {65, 153}, {46, 122}, {31, 107} for k = 0, 1, 2, 3. Every term (-1)^n / B'(lambda_n) is positive, and each class sum is 1/16291106900640 + 1/203460697440 = 1/203460697440 + 1/16291106900640 = 1/273136152240 + 1/760363989840 = 1/760363989840 + 1/273136152240 = 194/38984495395755. Hence R_0 = R_1 = R_2 = R_3 with M = 4 > 2, and M = N/2 lies outside the range M > N/2 for which the source states a proof.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.InClass`
- Truth anchor: `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.RateCondition`
- Truth anchor: `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.SpectrumCondition`
- Truth anchor: `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.derivativeAt`
- Truth anchor: `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.rateSum`
- Truth anchor: `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result`
