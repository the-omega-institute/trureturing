# Cao-Chen-Miller Egg-Drop Refutation

## Abstract

A correct bounded egg-drop strategy separates all hidden points by fixed-length binary transcripts. At four dimensions, five eggs, and side length five, the conjectured nine-drop budget has too few transcripts.

**Definition 1.1 (Critical points and query locations).**

$$\forall d \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; \operatorname{Point}\left(N\right) = \left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{Fin}\left(N\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.Point` (`✓ std3`).

*Citation.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

For side function N on Fin d, Point(N) is the dependent product of Fin(N(i)). The zero-based representatives encode the paper's coordinates 1 through N(i).

**Definition 1.2 (Broken-or-intact query outcome).**

$$\forall d \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; \forall q \in \operatorname{Point}\left(N\right),\; \forall x \in \operatorname{Point}\left(N\right),\; \operatorname{dropOutcome}\left(q, x\right) = \operatorname{if}\left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{val}\left(q\left(i\right)\right) < \operatorname{val}\left(x\left(i\right)\right), 1, 0\right)$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.dropOutcome` (`✓ std3`).

*Citation.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

The value is one exactly when every query coordinate is strictly below the corresponding hidden coordinate; otherwise it is zero.

**Definition 1.3 (Adaptive strategies with egg and drop budgets).**

$$\forall d \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; \begin{aligned}\operatorname{EggStrategy}\left(N\right) : \mathrm{Nat} \to \left(\mathrm{Nat} \to \mathrm{Type}\right),\\\operatorname{stop}\left(\right) : \forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \operatorname{Point}\left(N\right) \to \operatorname{EggStrategy}\left(N, e, h\right),\\\operatorname{drop}\left(\right) : \forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \operatorname{Point}\left(N\right) \to \left(\operatorname{EggStrategy}\left(N, e, h\right) \to \left(\operatorname{EggStrategy}\left(N, e + 1, h\right) \to \operatorname{EggStrategy}\left(N, e + 1, h + 1\right)\right)\right).\end{aligned}$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.EggStrategy` (`✓ std3`).

*Citation.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

A stop node returns a point at any remaining budget. A drop node asks one query, sends outcome zero to a child with one fewer egg, sends outcome one to a child with the same egg count, and consumes one drop.

**Definition 1.4 (Terminal prediction).**

$$\forall d \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; (\forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall g \in \operatorname{Point}\left(N\right),\; \forall x \in \operatorname{Point}\left(N\right),\; \operatorname{prediction}\left(\operatorname{stop}\left(g\right), x\right) = g) \land (\forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall q \in \operatorname{Point}\left(N\right),\; \forall b \in \operatorname{EggStrategy}\left(N, e, h\right),\; \forall t \in \operatorname{EggStrategy}\left(N, e + 1, h\right),\; \forall x \in \operatorname{Point}\left(N\right),\; \operatorname{prediction}\left(\operatorname{drop}\left(q, b, t\right), x\right) = \operatorname{if}\left(\operatorname{dropOutcome}\left(q, x\right) = 0, \operatorname{prediction}\left(b, x\right), \operatorname{prediction}\left(t, x\right)\right))$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.prediction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

Prediction follows the outcome-selected branch until a stop node and returns that node's point.

**Definition 1.5 (Fixed-length padded transcript).**

$$\forall d \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; (\forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall g \in \operatorname{Point}\left(N\right),\; \forall x \in \operatorname{Point}\left(N\right),\; \forall j \in \operatorname{Fin}\left(h\right),\; \operatorname{paddedTranscript}\left(\operatorname{stop}\left(g\right), x, j\right) = 0) \land \left((\forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall q \in \operatorname{Point}\left(N\right),\; \forall b \in \operatorname{EggStrategy}\left(N, e, h\right),\; \forall t \in \operatorname{EggStrategy}\left(N, e + 1, h\right),\; \forall x \in \operatorname{Point}\left(N\right),\; \operatorname{paddedTranscript}\left(\operatorname{drop}\left(q, b, t\right), x, 0\right) = \operatorname{dropOutcome}\left(q, x\right)) \land (\forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall q \in \operatorname{Point}\left(N\right),\; \forall b \in \operatorname{EggStrategy}\left(N, e, h\right),\; \forall t \in \operatorname{EggStrategy}\left(N, e + 1, h\right),\; \forall x \in \operatorname{Point}\left(N\right),\; \forall j \in \operatorname{Fin}\left(h\right),\; \operatorname{paddedTranscript}\left(\operatorname{drop}\left(q, b, t\right), x, \operatorname{succ}\left(j\right)\right) = \operatorname{if}\left(\operatorname{dropOutcome}\left(q, x\right) = 0, \operatorname{paddedTranscript}\left(b, x, j\right), \operatorname{paddedTranscript}\left(t, x, j\right)\right))\right)$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.paddedTranscript` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

The first coordinate at a drop node is its observed outcome. Later coordinates recurse into the selected child, while every coordinate after a stop node is zero. Thus every transcript has the full budgeted function type Fin h to Fin 2.

**Definition 1.6 (Exact recovery).**

$$\forall d \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; \forall e \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall s \in \operatorname{EggStrategy}\left(N, e, h\right),\; (\operatorname{Correct}\left(s\right)) \Leftrightarrow (\forall x \in \operatorname{Point}\left(N\right),\; \operatorname{prediction}\left(s, x\right) = x)$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.Correct` (`✓ std3`).

*Citation.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

A strategy is correct when its terminal prediction equals every possible hidden point.

**Definition 1.7 (The conjectured drop budget).**

$$\forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; \operatorname{paperBound}\left(d, k, N\right) = \operatorname{natCeil}\left((k - d + 1 : \mathrm{Real}) \cdot \operatorname{rpow}\left(\sum_{i \in \operatorname{Fin}\left(d\right)} ((N\left(i\right) : \mathrm{Real})), (k - d + 1 : \mathrm{Real})^{-1}\right)\right)$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.paperBound` (`✓ std3`).

*Citation.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

The natural offset k-d+1 and each side length are coerced to the reals. The exponent is the real inverse of the coerced offset, rpow is real exponentiation, and natCeil is the natural ceiling.

**Definition 1.8 (Universal budget assertion).**

$$(claim) \Leftrightarrow (\forall d \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall N \in \operatorname{Fin}\left(d\right) \to \mathrm{Nat},\; (1 \le d) \Rightarrow ((d \le k) \Rightarrow ((\forall i \in \operatorname{Fin}\left(d\right),\; 0 < N\left(i\right)) \Rightarrow (\exists s \in \operatorname{EggStrategy}\left(N, k, \operatorname{paperBound}\left(d, k, N\right)\right),\; \operatorname{Correct}\left(s\right)))))$$

*Formalization.* `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

For every positive dimension, sufficient egg count, and positive side function, claim asks for some correct strategy within paperBound. This existence statement is weaker than success of a particular named strategy.

**Theorem 1.9 (The universal assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cao-chen-miller-egg-drop-conjecture-one` (refuted) by `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cao-chen-miller-egg-drop-conjecture-one","declaration_gid":"D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xiangwen Cao and Zongyun Chen and Steven J. Miller (2025). *Egg Drop Problems: They Are All They Are Cracked Up To Be!*. DOI: [10.48550/arXiv.2511.18330](https://doi.org/10.48550/arXiv.2511.18330). URL: <https://arxiv.org/abs/2511.18330>.

*Commentary.*

At d=4, k=5, and constant side length five, paperBound is nine. Correctness makes paddedTranscript injective, but the hidden-point space has 625 elements and the nine-bit transcript space has 512.

## References

- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.Correct`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.EggStrategy`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.Point`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.claim`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.dropOutcome`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.paddedTranscript`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.paperBound`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.prediction`
- Truth anchor: `D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation.result`
