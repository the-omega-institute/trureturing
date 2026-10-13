# Exact density of diploid rule 10-245

## Abstract

For every mixing parameter in [0,1], diploid rule 10-245 has density 1/4 + λ/2 at every time from one onwards, starting from the fair Bernoulli cylinder law.

**Definition 1.1 (Elementary rule 10).**

$$\forall x \in \operatorname{Bool},\; \forall y \in \operatorname{Bool},\; \forall z \in \operatorname{Bool},\; \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.rule10}\left(x, y, z\right) = \operatorname{Bool.and}\left(\operatorname{Bool.not}\left(x\right), z\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.rule10` (`✓ std3`).

*Citation.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

For an ordered left, centre and right neighbourhood, rule 10 returns true exactly when the left spin is false and the right spin is true. The centre spin does not affect the output. Thus the neighbourhoods 001 and 011 give one, as in the rule 10-245 table of §3.2.

**Definition 1.2 (Elementary rule 245).**

$$\forall x \in \operatorname{Bool},\; \forall y \in \operatorname{Bool},\; \forall z \in \operatorname{Bool},\; \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.rule245}\left(x, y, z\right) = \operatorname{Bool.not}\left(\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.rule10}\left(x, y, z\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.rule245` (`✓ std3`).

*Citation.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

Rule 245 complements the output of rule 10. It returns zero on 001 and 011 and one on the other six neighbourhoods, giving the complementary rule in §3.2.

**Definition 1.3 (Conditional probability of a one).**

$$\forall lam \in \mathbb{R},\; \forall x \in \operatorname{Bool},\; \forall y \in \operatorname{Bool},\; \forall z \in \operatorname{Bool},\; \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.p}\left(lam, x, y, z\right) = (1 - lam) \cdot ((\operatorname{Bool.toNat}\left(\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.rule10}\left(x, y, z\right)\right): \mathbb{N}): \mathbb{R}) + lam \cdot ((\operatorname{Bool.toNat}\left(\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.rule245}\left(x, y, z\right)\right): \mathbb{N}): \mathbb{R})$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.p` (`✓ std3`).

*Citation.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

Equation (2) weights rule 10 by 1−λ and rule 245 by λ. In the order 000, 001, 010, 011, 100, 101, 110, 111, the probability of a one is λ, 1−λ, λ, 1−λ, λ, λ, λ, λ, exactly the table in §3.2. The formula defines a real-valued function for every real λ; probability laws below restrict λ to [0,1].

**Definition 1.4 (The binary update kernel).**

$$\forall lam \in \mathbb{R},\; \forall b \in \operatorname{Bool},\; \forall x \in \operatorname{Bool},\; \forall y \in \operatorname{Bool},\; \forall z \in \operatorname{Bool},\; \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.w}\left(lam, b, x, y, z\right) = \operatorname{ite}\left(b = \operatorname{Bool.true}, \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.p}\left(lam, x, y, z\right), 1 - \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.p}\left(lam, x, y, z\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.w` (`✓ std3`).

*Citation.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

The conditional probability in Eq. (1) is p for output true and 1−p for output false. For a fixed parent configuration, the cells use independent fresh choices of rule.

**Definition 1.5 (Evolution of finite cylinders).**

$$\forall lam \in \mathbb{R},\; \forall R \in ((n: \mathbb{N}) \to \left((\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{R}\right)),\; \forall n \in \mathbb{N},\; \forall b \in (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}),\; \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.evolve}\left(lam, R, n, b\right) = \sum_{(a: (\operatorname{Fin}\left(n + 2\right) \to \operatorname{Bool}))} ((\prod_{(j: \operatorname{Fin}\left(n\right))} (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.w}\left(lam, b\left(j\right), a\left(\operatorname{Fin.castSucc}\left(\operatorname{Fin.castSucc}\left(j\right)\right)\right), a\left(\operatorname{Fin.castSucc}\left(\operatorname{Fin.succ}\left(j\right)\right)\right), a\left(\operatorname{Fin.succ}\left(\operatorname{Fin.succ}\left(j\right)\right)\right)\right))) \cdot R\left(n + 2, a\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.evolve` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

A real cylinder family assigns a weight to every Boolean word of each length. To update a word of length n, sum over all parent words of length n+2, multiplying their weights by the n conditional update factors. The three Fin embeddings have values j, j+1 and j+2, so the two exterior parents are included without periodic indexing. This defines the cylinder evolution for the lattice process of §2, Eq. (1).

**Definition 1.6 (The Bernoulli cylinder hierarchy).**

$$\forall lam \in \mathbb{R},\; \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam\right) = \operatorname{Nat.rec}\left(motive := \lambda (\mathord{\cdot}: \mathbb{N}) \mapsto (((n: \mathbb{N}) \to \left((\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{R}\right))), \lambda (n: \mathbb{N}) \mapsto (\lambda (\mathord{\cdot}: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool})) \mapsto ((\frac{1}{((2: \mathbb{N}): \mathbb{R})})^{n})), \lambda (\mathord{\cdot}: \mathbb{N}) \mapsto (\lambda (R: ((n: \mathbb{N}) \to \left((\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{R}\right))) \mapsto (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.evolve}\left(lam, R\right)))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

Nat.rec starts at the fair Bernoulli weight (1/2)^n for each word of length n, the symmetric Bernoulli initial condition of §2. Its successor branch applies evolve to the preceding cylinder family. The denominator two is first a natural number and then cast to the real numbers. The hierarchy includes every finite word length and every natural time.

**Definition 1.7 (The density at a given time).**

$$\forall lam \in \mathbb{R},\; \forall t \in \mathbb{N},\; \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.d}\left(lam, t\right) = \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam, t, 1, \lambda (\mathord{\cdot}: \operatorname{Fin}\left(1\right)) \mapsto (\operatorname{Bool.true})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.d` (`✓ std3`).

*Citation.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

The density is the weight of the singleton cylinder whose spin is true. This is the expected spin value P_t(1) in §2, Eq. (3); it is an expectation, rather than a statement about the density along an individual realization.

**Definition 1.8 (Consistent finite probability laws).**

$$\forall lam \in \mathbb{R},\; (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.CylinderLaw}\left(lam\right)) \Leftrightarrow ((\forall t \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall b \in (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}),\; 0 \le \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam, t, n, b\right)) \land ((\forall t \in \mathbb{N},\; \forall n \in \mathbb{N},\; \sum_{(b: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}))} (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam, t, n, b\right)) = 1) \land ((\forall t \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall b \in (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}),\; \sum_{(c: \operatorname{Bool})} (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam, t, n + 1, \operatorname{Fin.snoc}\left(b, c\right)\right)) = \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam, t, n, b\right)) \land (\forall t \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall b \in (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}),\; \sum_{(c: \operatorname{Bool})} (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam, t, n + 1, \operatorname{Fin.cons}\left(c, b\right)\right)) = \operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.P}\left(lam, t, n, b\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.CylinderLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

At every time, each cylinder weight is nonnegative and the weights at each length sum to one. Summing over a new spin on either the right, using Fin.snoc, or the left, using Fin.cons, recovers the shorter cylinder weight. These are finite cylinder laws; no separate infinite-product probability space is part of this definition.

**Definition 1.9 (The exact-density proposition).**

$$(\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.claim}) \Leftrightarrow (\forall lam \in \mathbb{R},\; (lam \in \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.CylinderLaw}\left(lam\right)) \land ((\forall t \in \mathbb{N},\; (1 \le t) \Rightarrow (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.d}\left(lam, t\right) = \frac{1}{((4: \mathbb{N}): \mathbb{R})} + \frac{lam}{((2: \mathbb{N}): \mathbb{R})})) \land (\operatorname{Filter.Tendsto}\left(\lambda (t: \mathbb{N}) \mapsto (\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.d}\left(lam, t\right)), \operatorname{Filter.atTop}, \operatorname{nhds}\left(\frac{1}{((4: \mathbb{N}): \mathbb{R})} + \frac{lam}{((2: \mathbb{N}): \mathbb{R})}\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

Section 5 asks whether the asymptotic density 1/4 + λ/2 is exact for rule 10-245. This proposition strengthens that question: for every λ in the closed interval [0,1], the hierarchy satisfies CylinderLaw and the density equals 1/4 + λ/2 for every time t≥1. That identity implies the limit asked in §5, which is also stated explicitly. Both denominators are real casts of natural numerals.

**Theorem 1.10 (Exact density from time one).**

$$\operatorname{D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.result` (`✓ std3`). ∎

*Resolves.* `Problems/fuks-fates-2026-diploid-10-245-density` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fuks-fates-2026-diploid-10-245-density","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Henryk Fukś, Nazim Fatès (2026). *Analysis of the asymptotic density of endogamous diploid cellular automata*. DOI: [10.1140/epjs/s11734-026-02447-z](https://doi.org/10.1140/epjs/s11734-026-02447-z). URL: <https://arxiv.org/abs/2607.01917v1>.

*Commentary.*

The proposition holds for the cylinder hierarchy of Fukś–Fatès's rule 10-245, including λ=0 and λ=1. Summing out the independent output spins preserves both endpoint marginals, normalization and nonnegativity. The probability of a zero followed by a one at distance two stays equal to 1/4: its update is λ(1−λ) plus (1−2λ)^2 times its previous value, because the overlapping contributions vanish when a shared spin would have to be both zero and one. The next density is λ plus (1−2λ) times that distance-two probability, hence 1/4 + λ/2. Constancy from time one gives the stated limit. Constant density does not assert that the full cylinder family is stationary.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.CylinderLaw`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.P`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.d`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.evolve`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.p`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.rule10`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.rule245`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.w`
