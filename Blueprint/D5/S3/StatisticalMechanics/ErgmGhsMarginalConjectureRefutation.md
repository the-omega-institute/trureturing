# The marginal criterion does not imply GHS for general exponential random graphs

## Abstract

An edge-triangle Gibbs law has every edge marginal above one half and a positive third Ursell function.

**Definition 1.1 (Homomorphism density).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (h: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.homDensity}\left(h, g\right): \mathbb{R}) = \frac{(\operatorname{Nat.cast}\left(\operatorname{D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit.homCount}\left(h, g\right)\right): \mathbb{R})}{((\operatorname{Nat.cast}\left(n\right): \mathbb{R}))^{m}}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.homDensity` (`✓ std3`).

*Citation.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

For simple graphs h and g on m and n labeled vertices, respectively, homDensity is the number of adjacency-preserving vertex maps from h to g divided by n to the power m. The natural homomorphism count and n are cast to real numbers before division. This is the density in Section 2.1, TeX lines 292–296. The definition also includes n = 0, using total real division, so a zero denominator gives zero.

**Definition 1.2 (The homomorphism-density Hamiltonian).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (h: (\operatorname{Fin}\left(k\right)) \to (\Sigma (m: \mathbb{N}), (\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)))), (\forall (\beta: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.hamiltonian}\left(h, \beta, g\right): \mathbb{R}) = ((\operatorname{Nat.cast}\left(n\right): \mathbb{R}))^{2} \cdot \operatorname{dotProduct}\left(\beta, \lambda (j: \operatorname{Fin}\left(k\right)) \mapsto (\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.homDensity}\left(\operatorname{Sigma.snd}\left(h\left(j\right)\right), g\right))\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.hamiltonian` (`✓ std3`).

*Citation.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

A finite family h assigns to each index j a vertex count and a simple graph on that many vertices. The Hamiltonian multiplies the scalar product of the real coefficients β and the corresponding homomorphism densities by the square of the real cast of n. This is Section 2.1, TeX lines 298–308. The definition allows an empty family and coefficients of either sign.

**Definition 1.3 (The Gibbs probability of a graph).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (h: (\operatorname{Fin}\left(k\right)) \to (\Sigma (m: \mathbb{N}), (\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)))), (\forall (\beta: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.gibbsWeight}\left(h, \beta, g\right): \mathbb{R}) = \frac{\operatorname{Real.exp}\left(\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.hamiltonian}\left(h, \beta, g\right)\right)}{\sum_{(g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))} (\operatorname{Real.exp}\left(\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.hamiltonian}\left(h, \beta, g\right)\right))})))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.gibbsWeight` (`✓ std3`).

*Citation.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

The probability of a labeled simple graph g is the exponential of its Hamiltonian divided by the sum of these exponentials over all simple graphs on the same vertex set. This is the Gibbs density and partition sum of Section 2.1, TeX lines 300–312.

**Definition 1.4 (Expectation of a graph observable).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (h: (\operatorname{Fin}\left(k\right)) \to (\Sigma (m: \mathbb{N}), (\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)))), (\forall (\beta: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\forall (f: (\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, f\right): \mathbb{R}) = \operatorname{dotProduct}\left(\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.gibbsWeight}\left(h, \beta\right), f\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.expectation` (`✓ std3`).

*Citation.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

For a real observable f on labeled simple graphs, expectation is the scalar product of the Gibbs probabilities and f, hence their finite weighted sum. Section 4, TeX line 1248, uses expectation with respect to this general Gibbs law.

**Definition 1.5 (The indicator of a possible edge).**

$$\forall (n: \mathbb{N}), (\forall (e: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(e, g\right): \mathbb{R}) = \operatorname{Set.indicator}\left(\operatorname{SimpleGraph.edgeSet}\left(g\right), \operatorname{Function.const}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right), (1: \mathbb{R})\right), \operatorname{Subtype.val}\left(e\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.edgeIndicator` (`✓ std3`).

*Citation.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

An edge e of the complete graph is an unordered pair of distinct labeled vertices. Its indicator at g is one if that pair belongs to the edge set of g and zero otherwise. The constant function on unordered pairs is written as Function.const, and Subtype.val extracts the unordered pair underlying e. These are the edge coordinates described in Section 2.1, TeX lines 322–333.

**Definition 1.6 (The third Ursell function).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (h: (\operatorname{Fin}\left(k\right)) \to (\Sigma (m: \mathbb{N}), (\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)))), (\forall (\beta: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\forall (e: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), (\forall (f: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), (\forall (g: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), ((\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.u3}\left(h, \beta, e, f, g\right): \mathbb{R}) = \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \lambda (a: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(e, a\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(f, a\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(g, a\right))\right) - \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(e\right)\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \lambda (a: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(f, a\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(g, a\right))\right) - \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(f\right)\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \lambda (a: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(e, a\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(g, a\right))\right) - \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(g\right)\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \lambda (a: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(e, a\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(f, a\right))\right) + (2: \mathbb{R}) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(e\right)\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(f\right)\right) \cdot \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(g\right)\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.u3` (`✓ std3`).

*Citation.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

The third Ursell function is the third joint cumulant of the three edge indicators: the triple moment minus the three products of a marginal and the complementary pair moment, plus twice the product of the marginals. The edges e, f and g may coincide. The formula is given in Section 3, TeX lines 577–589; Definition 3.4, TeX lines 617–636, requires it to be nonpositive for every triple.

**Definition 1.7 (The universal marginal criterion).**

$$(\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (h: (\operatorname{Fin}\left(k + 1\right)) \to (\Sigma (m: \mathbb{N}), (\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)))), (\forall (\beta: (\operatorname{Fin}\left(k + 1\right)) \to (\mathbb{R})), ((h\left((0: \operatorname{Fin}\left(k + 1\right))\right) = (((2: \mathbb{N}), (\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(2\right)\right))): \Sigma (m: \mathbb{N}), (\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)))) \to ((\forall (j: \operatorname{Fin}\left(k + 1\right)), ((j \ne (0: \operatorname{Fin}\left(k + 1\right))) \to ((0: \mathbb{R}) \le \beta\left(j\right)))) \to ((\forall (e: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), ((\frac{1}{2}: \mathbb{R}) \le \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.expectation}\left(h, \beta, \operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.edgeIndicator}\left(e\right)\right))) \Leftrightarrow (\forall (e: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), (\forall (f: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), (\forall (g: \operatorname{Subtype}\left(\operatorname{SimpleGraph.edgeSet}\left((\operatorname{Top.top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)), (\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.u3}\left(h, \beta, e, f, g\right) \le (0: \mathbb{R}))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

For every natural n and every nonempty finite family indexed by Fin (k + 1), the first graph is the complete graph on two vertices. Its coefficient is unrestricted; every coefficient at a nonzero index is nonnegative. Under these hypotheses the proposition asserts that all edge marginals are at least one half if and only if all third Ursell functions are nonpositive, including triples with repeated edges. This states the conjectured equivalence at TeX line 1322 with the general setting of Section 4, TeX lines 1248–1264, made explicit. The quantification includes n = 0 and n = 1, whose complete graphs have no edges.

**Theorem 1.8 (Three vertices refute the sufficiency direction).**

$$\neg (\operatorname{D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bianchi-collet-magnanini-2022-ergm-ghs-marginal` (refuted) by `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bianchi-collet-magnanini-2022-ergm-ghs-marginal","declaration_gid":"D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alessandra Bianchi; Francesca Collet; Elena Magnanini (2022). *The GHS and other correlation inequalities for the two-star model*. DOI: [10.30757/ALEA.v19-64](https://doi.org/10.30757/ALEA.v19-64). URL: <https://arxiv.org/abs/2107.08889v2>.

*Commentary.*

Take n = 3, k = 1, h(0) = K₂ and h(1) = K₃, with β(0) = 0 and β(1) = log(2)/2. A homomorphism from K₃ to a simple graph on three vertices is injective, because distinct vertices of K₃ are adjacent and a simple graph has no loops. It is therefore surjective. Its image contains every possible edge, so the target must be K₃. The six permutations of its vertices give all such maps to K₃, and there are none to any other target. Substitution into the Hamiltonian gives 3²(log(2)/2)(6/3³) = log(2) at K₃ and zero at each other graph.

Encode each graph by the three Boolean choices for the unordered pairs {0,1}, {0,2} and {1,2}. Reading these three adjacencies recovers the choices, and choosing the three adjacencies of an arbitrary graph reconstructs that graph. Thus this is a bijection with the eight Boolean triples; K₃ corresponds exactly to the triple with all entries true. Reindexing the graph sums by this bijection, the exponential weight is two at K₃ and one at the other seven graphs. The partition sum is nine, so their probabilities are 2/9 and 1/9, respectively.

Each edge belongs to four graphs, one of which is K₃, so its marginal is (1 + 1 + 1 + 2)/9 = 5/9. Each pair of distinct edges belongs to two graphs, including K₃, so its joint moment is (1 + 2)/9 = 1/3. All three edges occur together only in K₃, giving triple moment 2/9. For the triple consisting of {0,1}, {0,2} and {1,2}, substitution into the third Ursell formula gives 2/9 − 3(5/9)(1/3) + 2(5/9)³ = 7/729.

Suppose the universal equivalence holds. The only nonzero index is one, and its coefficient log(2)/2 is nonnegative since log(2) is nonnegative. Every edge marginal is 5/9 ≥ 1/2. Applying the forward implication at n = 3 and k = 1 therefore makes the third Ursell function nonpositive at the three distinct edges. This contradicts 7/729 > 0. Hence the marginal lower bounds do not suffice for GHS in this general family.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.edgeIndicator`
- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.expectation`
- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.gibbsWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.hamiltonian`
- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.homDensity`
- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.u3`
- Dependency: [D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit](../Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.md)
