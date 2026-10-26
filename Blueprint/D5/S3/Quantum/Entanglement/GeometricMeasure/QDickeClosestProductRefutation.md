# Closest product vectors need not be q-symmetric

## Abstract

At q equal to four, no closest normalized product vector to the one-excitation three-qubit q-Dicke state is q-symmetric.

**Definition 1.1 (The one-excitation q-Dicke vector).**

$$\forall (q: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.dicke1}\left(q\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))\right)) = \operatorname{WithLp.toLp}\left(2, \lambda (p: (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))) \mapsto (\frac{\operatorname{ite}\left(p = ((0: \operatorname{Fin}\left(2\right)), ((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))), \operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(q\right)\right), \operatorname{ite}\left(p = ((0: \operatorname{Fin}\left(2\right)), ((1: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))), (1: \mathbb{C}), \operatorname{ite}\left(p = ((1: \operatorname{Fin}\left(2\right)), ((0: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))), \operatorname{Inv.inv}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(q\right)\right)\right), (0: \mathbb{C})\right)\right)\right)}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(q + (1: \mathbb{R}) + \operatorname{Inv.inv}\left(q\right)\right)\right)})\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.dicke1` (`✓ std3`).

*Citation.* Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio (2025). *Deformations of the symmetric subspace of qubit chains*. DOI: [10.1088/1751-8121/ae05da](https://doi.org/10.1088/1751-8121/ae05da). URL: <https://arxiv.org/abs/2503.23554v3>.

*Commentary.*

With zero denoting down and one denoting up, the nonzero coordinates are at (0,0,1), (0,1,0) and (1,0,0), with respective coefficients sqrt(q), one and the inverse of sqrt(q), divided by sqrt(q + 1 + q inverse). For positive q this is the normalized one-excitation state in the v3 TeX, line 581; the q-number at line 469 gives [3]_q = q + 1 + q inverse. The formula defines a vector for every real q, without asserting normalization outside the positive range. Complex.ofReal explicitly includes each real square root in the complex scalars.

**Definition 1.2 (The two-excitation q-Dicke vector).**

$$\forall (q: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.dicke2}\left(q\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))\right)) = \operatorname{WithLp.toLp}\left(2, \lambda (p: (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))) \mapsto (\frac{\operatorname{ite}\left(p = ((0: \operatorname{Fin}\left(2\right)), ((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))), \operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(q\right)\right), \operatorname{ite}\left(p = ((1: \operatorname{Fin}\left(2\right)), ((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))), (1: \mathbb{C}), \operatorname{ite}\left(p = ((1: \operatorname{Fin}\left(2\right)), ((1: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))), \operatorname{Inv.inv}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(q\right)\right)\right), (0: \mathbb{C})\right)\right)\right)}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(q + (1: \mathbb{R}) + \operatorname{Inv.inv}\left(q\right)\right)\right)})\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.dicke2` (`✓ std3`).

*Citation.* Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio (2025). *Deformations of the symmetric subspace of qubit chains*. DOI: [10.1088/1751-8121/ae05da](https://doi.org/10.1088/1751-8121/ae05da). URL: <https://arxiv.org/abs/2503.23554v3>.

*Commentary.*

The two-excitation vector has the same three coefficients and denominator, now at (0,1,1), (1,0,1) and (1,1,0). For positive q this is the normalized state in the v3 TeX, line 582. Its displayed expression is defined for every real q.

**Definition 1.3 (The three-qubit q-symmetric span).**

$$\forall (q: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.symQ}\left(q\right): \operatorname{Submodule}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))\right)\right)) = \operatorname{Submodule.span}\left(\mathbb{C}, \{\operatorname{EuclideanSpace.single}\left(((0: \operatorname{Fin}\left(2\right)), ((0: \operatorname{Fin}\left(2\right)), (0: \operatorname{Fin}\left(2\right)))), (1: \mathbb{C})\right), \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.dicke1}\left(q\right), \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.dicke2}\left(q\right), \operatorname{EuclideanSpace.single}\left(((1: \operatorname{Fin}\left(2\right)), ((1: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right)))), (1: \mathbb{C})\right)\}\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.symQ` (`✓ std3`).

*Citation.* Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio (2025). *Deformations of the symmetric subspace of qubit chains*. DOI: [10.1088/1751-8121/ae05da](https://doi.org/10.1088/1751-8121/ae05da). URL: <https://arxiv.org/abs/2503.23554v3>.

*Commentary.*

Take the complex linear span of the all-zero coordinate vector, the one-excitation and two-excitation vectors, and the all-one coordinate vector. For positive q this is the three-qubit q-symmetric subspace described in the v3 TeX, lines 579–586. The definition itself allows every real q.

**Definition 1.4 (An ordinary three-qubit product vector).**

$$\forall (a: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\forall (b: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\forall (c: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.prod}\left(a, b, c\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))\right)) = \operatorname{WithLp.toLp}\left(2, \lambda (p: (\operatorname{Fin}\left(2\right) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))) \mapsto (\operatorname{WithLp.ofLp}\left(a, (p).1\right) \cdot \operatorname{WithLp.ofLp}\left(b, ((p).2).1\right) \cdot \operatorname{WithLp.ofLp}\left(c, ((p).2).2\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.prod` (`✓ std3`).

*Citation.* Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio (2025). *Deformations of the symmetric subspace of qubit chains*. DOI: [10.1088/1751-8121/ae05da](https://doi.org/10.1088/1751-8121/ae05da). URL: <https://arxiv.org/abs/2503.23554v3>.

*Commentary.*

Multiply the three local complex coordinates to form the ordinary tensor product, as in the v3 TeX, lines 1238–1242. The index is the right-associated pair (p.1,(p.2.1,p.2.2)); WithLp.ofLp gives the coordinate function of each Euclidean vector. No unit-norm condition is part of this definition.

**Definition 1.5 (Maximal overlap among normalized product vectors).**

$$\forall (q: \mathbb{R}), (\forall (a: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\forall (b: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\forall (c: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.IsClosestProduct}\left(q, a, b, c\right): \operatorname{Prop}) = ((\left\lVert a \right\rVert = (1: \mathbb{R})) \land ((\left\lVert b \right\rVert = (1: \mathbb{R})) \land ((\left\lVert c \right\rVert = (1: \mathbb{R})) \land (\forall (a': \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\forall (b': \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\forall (c': \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), ((\left\lVert a' \right\rVert = (1: \mathbb{R})) \Rightarrow ((\left\lVert b' \right\rVert = (1: \mathbb{R})) \Rightarrow ((\left\lVert c' \right\rVert = (1: \mathbb{R})) \Rightarrow (\left\lVert \operatorname{inner}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.dicke1}\left(q\right), \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.prod}\left(a', b', c'\right)\right) \right\rVert \le \left\lVert \operatorname{inner}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.dicke1}\left(q\right), \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.prod}\left(a, b, c\right)\right) \right\rVert))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.IsClosestProduct` (`✓ std3`).

*Citation.* Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio (2025). *Deformations of the symmetric subspace of qubit chains*. DOI: [10.1088/1751-8121/ae05da](https://doi.org/10.1088/1751-8121/ae05da). URL: <https://arxiv.org/abs/2503.23554v3>.

*Commentary.*

The three local vectors have norm one, and their product has overlap modulus with dicke1 q at least as large as that of every other normalized product. This specializes the geometric optimization in the v3 TeX, lines 1234–1243, to the one-excitation three-qubit state. The inner product and all local norms are the ordinary complex Euclidean ones.

**Definition 1.6 (A q-symmetric closest product for every positive deformation).**

$$\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.claim} = (\forall (q: \mathbb{R}), (((0: \mathbb{R}) < q) \Rightarrow (\exists (a: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\exists (b: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), (\exists (c: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(2\right)\right)), ((\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.IsClosestProduct}\left(q, a, b, c\right)) \land (\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.prod}\left(a, b, c\right) \in \operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.symQ}\left(q\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio (2025). *Deformations of the symmetric subspace of qubit chains*. DOI: [10.1088/1751-8121/ae05da](https://doi.org/10.1088/1751-8121/ae05da). URL: <https://arxiv.org/abs/2503.23554v3>.

*Commentary.*

For every positive real q, some normalized product maximizing the ordinary overlap with dicke1 q belongs to the q-symmetric span. This is the one-excitation, three-qubit instance of the conjecture for arbitrary q-Dicke states in the v3 TeX, line 1258.

**Theorem 1.7 (The obstruction at q equal to four).**

$$\neg (\operatorname{D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ballesteros-et-al-2025-qdicke-closest-product` (refuted) by `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ballesteros-et-al-2025-qdicke-closest-product","declaration_gid":"D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio (2025). *Deformations of the symmetric subspace of qubit chains*. DOI: [10.1088/1751-8121/ae05da](https://doi.org/10.1088/1751-8121/ae05da). URL: <https://arxiv.org/abs/2503.23554v3>.

*Commentary.*

For a unit complex qubit, the squared moduli of its two coordinates sum to one. The squared scalar Cauchy–Schwarz inequality bounds the squared modulus of xu + yv by the product of the squared coordinate norms of (x,y) and (u,v). These two facts control all the product overlaps below.

At q = 4 the one-excitation vector is (4|001> + 2|010> + |100>)/sqrt(21). Its inner product with prod a b c is (4 a(0)b(0)c(1) + (2 a(0)b(1) + a(1)b(0))c(0))/sqrt(21). Squaring its modulus and multiplying by 21 therefore gives the squared modulus of this numerator.

For unit a,b,c, apply Cauchy–Schwarz first to the numerator with the coordinates c(1),c(0), and then to 2 a(0)b(1) + a(1)b(0) with coefficients 2,1. Put A = |a(0)| squared and B = |b(0)| squared. Normalization gives 21 times the squared overlap at most 16AB + 5(A(1-B) + (1-A)B) = 5A + 5B + 6AB.

The normalized product |0> tensor |0> tensor |1> has squared overlap 16/21. Any maximizing triple a,b,c consequently has squared overlap at least 16/21. Since A and B each lie between zero and one, AB is at most one; the preceding bound then forces A = B = 1. Thus a(1) = b(1) = 0. The squared-overlap identity and normalization of c force |c(1)| squared to equal one and c(0) = 0. In particular a(0)b(0)c(1) is nonzero.

Every vector v in symQ 4 satisfies v(0,0,1) = 2 v(0,1,0). Indeed, the complex linear functional taking v to v(0,0,1) - 2 v(0,1,0) vanishes on each of the four spanning vectors. The all-zero, all-one and two-excitation vectors have both coordinates zero; dicke1 4 has coordinates 4/sqrt(21) and 2/sqrt(21). Their span therefore lies in its kernel. For a maximizing product, membership in this span would give a(0)b(0)c(1) = 2 a(0)b(1)c(0) = 0, contradicting the nonzero product just obtained. Finally, the asserted universal existence at positive q would supply such a maximizing product in the span at q = 4, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.IsClosestProduct`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.dicke1`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.dicke2`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.prod`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.symQ`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../AbsoluteSeparability/LowRankRays.md)
- Dependency: [D5/S3/Quantum/Measurement/DelayedRemoteControlDimensionWitness](../../Measurement/DelayedRemoteControlDimensionWitness.md)
