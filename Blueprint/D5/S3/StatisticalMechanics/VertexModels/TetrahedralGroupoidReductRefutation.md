# A T1-groupoid whose reduct is not reduced

## Abstract

A first tetrahedral groupoid can have a reduct that is not a reduced first tetrahedral groupoid. On Bool, take circ to be conjunction and star, lt and rt to be left projections. This answers the question in Section 9.2 of Bardakov et al., arXiv:2206.08906v1.

**Definition 1.1 (The four-operation axioms).**

$$\forall X \in \operatorname{Type},\; \forall star \in X \to (X \to X),\; \forall circ \in X \to (X \to X),\; \forall lt \in X \to (X \to X),\; \forall rt \in X \to (X \to X),\; \operatorname{IsT1Groupoid}\left(star, circ, lt, rt\right) \Leftrightarrow ((\forall x \in X,\; \forall y \in X,\; \forall z \in X,\; circ\left(x, y\right) = circ\left(lt\left(x, z\right), lt\left(y, z\right)\right)) \land ((\forall x \in X,\; \forall y \in X,\; \forall z \in X,\; \forall w \in X,\; star\left(circ\left(x, y\right), circ\left(z, w\right)\right) = circ\left(star\left(x, z\right), star\left(y, w\right)\right)) \land ((\forall x \in X,\; \forall y \in X,\; \forall z \in X,\; rt\left(rt\left(x, y\right), z\right) = rt\left(rt\left(x, z\right), star\left(y, z\right)\right)) \land (\forall x \in X,\; \forall y \in X,\; \forall z \in X,\; lt\left(star\left(x, y\right), z\right) = rt\left(x, circ\left(y, z\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.IsT1Groupoid` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

For a type X and four binary operations star, circ, lt and rt on X, IsT1Groupoid is the conjunction of these four identities, in the printed order. The operations star, circ, lt and rt denote the paper's star, circle, left triangle and right triangle operations.

**Definition 1.2 (The two-operation axioms).**

$$\forall X \in \operatorname{Type},\; \forall star \in X \to (X \to X),\; \forall circ \in X \to (X \to X),\; \operatorname{IsReducedT1Groupoid}\left(star, circ\right) \Leftrightarrow ((\forall x \in X,\; \forall y \in X,\; \forall z \in X,\; circ\left(x, y\right) = circ\left(circ\left(x, z\right), circ\left(y, z\right)\right)) \land ((\forall x \in X,\; \forall y \in X,\; \forall z \in X,\; star\left(star\left(x, y\right), z\right) = star\left(star\left(x, z\right), star\left(y, z\right)\right)) \land (\forall x \in X,\; \forall y \in X,\; \forall z \in X,\; \forall w \in X,\; star\left(circ\left(x, y\right), circ\left(z, w\right)\right) = circ\left(star\left(x, z\right), star\left(y, w\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.IsReducedT1Groupoid` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

For a type X and binary operations star and circ on X, IsReducedT1Groupoid is the conjunction of these three identities, in the printed order. Its first identity constrains circ itself, whereas the first four-operation identity uses lt in both arguments of circ.

**Definition 1.3 (The universal reduct assertion).**

$$\operatorname{claim} \Leftrightarrow (\forall X \in \operatorname{Type},\; \forall star \in X \to (X \to X),\; \forall circ \in X \to (X \to X),\; \forall lt \in X \to (X \to X),\; \forall rt \in X \to (X \to X),\; \operatorname{IsT1Groupoid}\left(star, circ, lt, rt\right) \Rightarrow \operatorname{IsReducedT1Groupoid}\left(star, circ\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.claim` (`✓ std3`).

*Citation.* V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov (2024). *Set-Theoretical Solutions of the n-Simplex Equation*. DOI: [10.1134/S1055134424010012](https://doi.org/10.1134/S1055134424010012). URL: <https://arxiv.org/abs/2206.08906v1>.

*Commentary.*

The assertion says that for every type X and all four binary operations on X, the four T1 identities imply the three reduced identities after forgetting lt and rt.

**Theorem 1.4 (The assertion is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bardakov-2022-t1-groupoid-reduct-question` (refuted) by `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bardakov-2022-t1-groupoid-reduct-question","declaration_gid":"D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Set X = Bool, circ(x, y) = x && y, and star(x, y) = lt(x, y) = rt(x, y) = x. The two sides of each of the first two T1 identities equal x && y, and the two sides of each of the last two equal x. The first reduced identity at x = y = true and z = false would equate true with false. Thus these operations form a T1-groupoid whose reduct is not reduced.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.IsReducedT1Groupoid`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.IsT1Groupoid`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.result`
