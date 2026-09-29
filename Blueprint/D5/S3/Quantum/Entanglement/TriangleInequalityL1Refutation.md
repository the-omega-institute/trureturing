# A local counterexample to the triangle inequality ineq_l1

## Abstract

The inequality s_111(p) - 0.475 Delta_1(p) <= 0.289, which E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner (arXiv:2405.08939, eq. ineq_l1) state should hold for every distribution that is local in the triangle network, fails: a local model with four outcomes per party has Delta_1 = 0 and s_111 = 11/36.

**Definition 1.1 (Outcome type).**

$$\operatorname{outcomeType}\left(a, b, c\right) = \left|\{a, b, c\}\right|$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.outcomeType` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The number of distinct outcomes among a, b, c: 1 for the type 111, 2 for the type 112 and 3 for the type 123. The three types contain 4, 36 and 24 outcome triples.

**Definition 1.2 (Mean over an outcome type).**

$$\operatorname{typeMean}\left(p, m\right) = \frac{\sum_{(a, b, c) \in \operatorname{Fin}\left(4\right)^{3}, \operatorname{outcomeType}\left(a, b, c\right) = m} p\left(a, b, c\right)}{\left|\{(a, b, c) \in \operatorname{Fin}\left(4\right)^{3} \mid \operatorname{outcomeType}\left(a, b, c\right) = m\}\right|}$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.typeMean` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

M_X of the paper: the mean of p over the outcome triples of type m.

**Definition 1.3 (Asymmetry penalty).**

$$\operatorname{deltaL1}\left(p\right) = \sum_{a} \sum_{b} \sum_{c} \left|\operatorname{typeMean}\left(p, \operatorname{outcomeType}\left(a, b, c\right)\right) - p\left(a, b, c\right)\right|$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.deltaL1` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

Delta_{l=1} of the paper: the absolute deviations of p from the mean of its outcome type, summed over the three types.

**Definition 1.4 (The inequality ineq_l1).**

$$claim \Leftrightarrow (\forall p \in \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(4\right) \to \mathbb{R},\; (\operatorname{IsTriangleLocal}\left(p\right)) \Rightarrow \operatorname{s111}\left(p\right) - \frac{475}{1000} \cdot \operatorname{deltaL1}\left(p\right) \le \frac{289}{1000})$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.claim` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

Eq. (ineq_l1) of the paper with its printed constants 0.475 and 0.289, for every distribution that is local in the triangle network in the sense of eq. (trilocal).

**Theorem 1.5 (A local distribution violating ineq_l1).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/baumer-2024-triangle-inequality-l1` (refuted) by `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baumer-2024-triangle-inequality-l1","declaration_gid":"D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

Let each source send one of the 24 orderings x = (x_1, x_2, x_3, x_4) of the four outcomes, uniformly, and let every party apply one rule f to its two sources in cyclic order: A = f(beta, gamma), B = f(gamma, alpha), C = f(alpha, beta). If x_1 or x_2 stands in one of the first two places of y, f(x, y) is whichever of them comes first in y; otherwise f(x, y) is x_1 if x_1 precedes x_2 in y, and x_3 if not. Cutting [0, 1] into 24 equal cells turns this into responses on [0, 1], and as for the fully symmetric model of the same paper the integral factorises over the cells, so p(a, b, c) is the number of source triples with outputs (a, b, c) divided by 24^3 = 13824. Sixteen kernel-checked counts over the 13824 triples give 1056 when a = b = c, 148 when exactly two outputs agree and 178 when all differ. So p is constant on each outcome type, every deviation from the type mean vanishes and Delta_1(p) = 0, while s_111(p) = 4 * 1056 / 13824 = 11/36 > 0.289.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.deltaL1`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.outcomeType`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.typeMean`
- Dependency: [D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation](TriangleSymmetricLocalRefutation.md)
