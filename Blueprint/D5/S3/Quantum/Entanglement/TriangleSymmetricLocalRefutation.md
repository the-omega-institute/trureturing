# A fully symmetric triangle-local distribution with p(A = B = C) above 1/4

## Abstract

There is a distribution that is local in the triangle network and fully symmetric, with four outcomes per party, such that p(A = B = C) = 41/144 > 1/4. This answers yes the open problem of E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner (arXiv:2405.08939), whose best local construction reached 1/4.

**Definition 1.1 (Locality in the triangle network).**

$$\operatorname{IsTriangleLocal}\left(p\right) \Leftrightarrow (\exists p_{A}, p_{B}, p_{C} : \operatorname{Fin}\left(4\right) \to \mathbb{R} \to \mathbb{R} \to \mathbb{R}, (\forall a \in \operatorname{Fin}\left(4\right),\; \operatorname{Measurable}\left(\operatorname{uncurry}\left(\left(p_{A}\right)\left(a\right)\right)\right)) \land \left((\forall a \in \operatorname{Fin}\left(4\right),\; \operatorname{Measurable}\left(\operatorname{uncurry}\left(\left(p_{B}\right)\left(a\right)\right)\right)) \land \left((\forall a \in \operatorname{Fin}\left(4\right),\; \operatorname{Measurable}\left(\operatorname{uncurry}\left(\left(p_{C}\right)\left(a\right)\right)\right)) \land \left((\forall a \in \operatorname{Fin}\left(4\right),\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 \le \left(p_{A}\right)\left(a, x, y\right)) \land \left((\forall a \in \operatorname{Fin}\left(4\right),\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 \le \left(p_{B}\right)\left(a, x, y\right)) \land \left((\forall a \in \operatorname{Fin}\left(4\right),\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; 0 \le \left(p_{C}\right)\left(a, x, y\right)) \land \left((\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \sum_{a} \left(p_{A}\right)\left(a, x, y\right) = 1) \land \left((\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \sum_{a} \left(p_{B}\right)\left(a, x, y\right) = 1) \land \left((\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \sum_{a} \left(p_{C}\right)\left(a, x, y\right) = 1) \land (\forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \forall c \in \operatorname{Fin}\left(4\right),\; p\left(a, b, c\right) = \int_{[0,1]^{3}} \left(p_{A}\right)\left(a, \beta, \gamma\right) \cdot \left(p_{B}\right)\left(b, \gamma, \alpha\right) \cdot \left(p_{C}\right)\left(c, \alpha, \beta\right) d\alpha d\beta d\gamma)\right)\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.IsTriangleLocal` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

Eq. (trilocal) of the paper: the three sources are uniform on [0, 1], Alice's output depends on the sources beta and gamma, Bob's on gamma and alpha, and Charlie's on alpha and beta. The responses p_A, p_B and p_C are measurable conditional distributions over the four outcomes: each is measurable in its two source values, nonnegative, and sums to 1 over the outcome.

**Definition 1.2 (Fully symmetric distributions).**

$$\operatorname{FullySymmetric}\left(p\right) \Leftrightarrow ((\forall \pi \in \operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right), \forall o \in \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(4\right),\; p\left(o\left(\pi\left(0\right)\right), o\left(\pi\left(1\right)\right), o\left(\pi\left(2\right)\right)\right) = p\left(o\left(0\right), o\left(1\right), o\left(2\right)\right)) \land (\forall \sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(4\right)\right), \forall a \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \forall c \in \operatorname{Fin}\left(4\right),\; p\left(\sigma\left(a\right), \sigma\left(b\right), \sigma\left(c\right)\right) = p\left(a, b, c\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.FullySymmetric` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

Invariance under every permutation of the three parties and under every joint relabelling of the four outcomes.

**Definition 1.3 (Probability that all outputs agree).**

$$\operatorname{s111}\left(p\right) = \sum_{k} p\left(k, k, k\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.s111` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The quantity s_111 = p(A = B = C) of the paper.

**Definition 1.4 (The bound one quarter).**

$$claim \Leftrightarrow (\forall p \in \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(4\right) \to \mathbb{R},\; (\operatorname{IsTriangleLocal}\left(p\right)) \Rightarrow \left((\operatorname{FullySymmetric}\left(p\right)) \Rightarrow \operatorname{s111}\left(p\right) \le \frac{1}{4}\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.claim` (`✓ std3`).

*Citation.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The negative answer to the open problem: every local fully symmetric distribution has p(A = B = C) at most 1/4.

**Theorem 1.5 (A local fully symmetric distribution above one quarter).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/baumer-2024-triangle-symmetric-local-quarter` (refuted) by `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baumer-2024-triangle-symmetric-local-quarter","declaration_gid":"D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv.2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

Let each source send one of the 12 ordered pairs x = (x_1, x_2) of distinct outcomes, uniformly, and let every party apply the rule f(x, y) = x_2 if x_2 is one of y_1, y_2, and x_1 otherwise, to its two sources in cyclic order: A = f(beta, gamma), B = f(gamma, alpha), C = f(alpha, beta). Cutting [0, 1] into 12 equal cells turns this into responses on [0, 1]; each cell has measure 1/12 and the integral factorises over the cells, so p(a, b, c) is the number of source triples with outputs (a, b, c) divided by 12^3 = 1728. A kernel-checked count over the 1728 triples gives 123 when a = b = c, 19 when exactly two outputs agree and 23 when all differ. This depends only on how many outputs are distinct, which neither a relabelling of the outcomes nor a permutation of the parties changes, so p is fully symmetric, and p(A = B = C) = 4 * 123 / 1728 = 41/144 > 1/4.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.FullySymmetric`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.IsTriangleLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.s111`
