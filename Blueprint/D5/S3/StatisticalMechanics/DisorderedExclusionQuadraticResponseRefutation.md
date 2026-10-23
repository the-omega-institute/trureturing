# Vanishing quadratic response without either rate symmetry

## Abstract

A four-site exclusion ring has zero quadratic current response despite failing both proposed rate-symmetry conditions.

The sites form Fin L, the residues 0 through L − 1, with addition and subtraction modulo L. A configuration is a finite subset of occupied sites; at most one particle occupies a site. Finset.card counts occupied sites, Finset.erase removes a site, and insert adds one. Sums and products with a displayed type range over every element of that finite type; a sum over i in s ranges only over the occupied sites. The anonymous assumption [NeZero L] requires L to be nonzero. The rates wp and wm and all probabilities are real-valued. The definitions allow arbitrary real bias; positive hopping rates describe the exclusion process when wp and wm are positive and −1 < ε < 1.

**Definition 1.1 (Rightward hopping rates).**

$$\forall (L: \mathbb{N}), (\forall (wp: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(L\right)), (\operatorname{p}\left(wp, \varepsilon, i\right) = \frac{1 + \varepsilon}{2} \cdot wp\left(i\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.p` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

Equation (1) multiplies the rightward trap or bond rate wp(i) by (1 + ε)/2. A positive ε favours hopping from i to i + 1.

**Definition 1.2 (Leftward hopping rates).**

$$\forall (L: \mathbb{N}), (\forall (wm: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(L\right)), (\operatorname{q}\left(wm, \varepsilon, i\right) = \frac{1 - \varepsilon}{2} \cdot wm\left(i\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

Equation (1) multiplies the leftward rate wm(i) by (1 − ε)/2. A particle at i attempts a hop to i − 1 with this rate.

**Definition 1.3 (Transitions between exclusion configurations).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)], (\forall (wp: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (wm: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (\forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)), (\forall (t: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)), (\operatorname{rate}\left(wp, wm, \varepsilon, s, t\right) = \sum_{i \in s} ((\operatorname{if} ((\neg (i + 1 \in s)) \land (t = \operatorname{insert}\left(i + 1, \operatorname{Finset.erase}\left(s, i\right)\right))) \operatorname{then} (\operatorname{p}\left(wp, \varepsilon, i\right)) \operatorname{else} (0)) + (\operatorname{if} ((\neg (i - 1 \in s)) \land (t = \operatorname{insert}\left(i - 1, \operatorname{Finset.erase}\left(s, i\right)\right))) \operatorname{then} (\operatorname{q}\left(wm, \varepsilon, i\right)) \operatorname{else} (0))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.rate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

Each occupied site contributes its rightward and leftward rates precisely when the destination is empty and moving that particle produces t. The two contributions are added, including when both directions lead to the same configuration. These are the single-particle transitions of the exclusion ring in Section II.

**Definition 1.4 (The stationary probability law).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)], (\forall (N: \mathbb{N}), (\forall (wp: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (wm: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (\forall (\mu: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right) \to \mathbb{R}), ((\operatorname{IsStationary}\left(N, wp, wm, \varepsilon, \mu\right)) \Leftrightarrow ((\forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)), ((\operatorname{Finset.card}\left(s\right) \ne N) \Rightarrow (\mu\left(s\right) = 0))) \land ((\forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)), (0 \le \mu\left(s\right))) \land ((\sum_{(s: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right))} (\mu\left(s\right)) = 1) \land (\forall (t: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right)), (\sum_{(s: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right))} (\mu\left(s\right) \cdot \operatorname{rate}\left(wp, wm, \varepsilon, s, t\right)) = \mu\left(t\right) \cdot \sum_{(s: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right))} (\operatorname{rate}\left(wp, wm, \varepsilon, t, s\right))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.IsStationary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

A stationary law vanishes outside configurations with N particles, is nonnegative everywhere, and has total mass one. For every target configuration t, the incoming probability flux equals the outgoing flux. Both balance sums range over all finite subsets of the ring. This gives the finite-state stationary law for the dynamics of Section II.

**Definition 1.5 (Current across the bond from 0 to 1).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)], (\forall (wp: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (wm: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (\forall (\mu: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right) \to \mathbb{R}), (\operatorname{current}\left(wp, wm, \varepsilon, \mu\right) = \sum_{(s: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right))} (\mu\left(s\right) \cdot \left((\operatorname{if} ((0 \in s) \land (\neg (1 \in s))) \operatorname{then} (\operatorname{p}\left(wp, \varepsilon, 0\right)) \operatorname{else} (0)) - (\operatorname{if} ((1 \in s) \land (\neg (0 \in s))) \operatorname{then} (\operatorname{q}\left(wm, \varepsilon, 1\right)) \operatorname{else} (0))\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.current` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

The expectation of the rightward hopping rate minus the leftward hopping rate gives the current across the bond (0,1). A hop contributes only when its origin is occupied and its destination is empty. Under a stationary law this is the bond current of equation (2), written as the occupation-probability expression in Appendix C, equation (C1).

**Definition 1.6 (Condition (i): the same ratio on every bond).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)], (\forall (wp: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (wm: \operatorname{Fin}\left(L\right) \to \mathbb{R}), ((\operatorname{BondRatioUniform}\left(wp, wm\right)) \Leftrightarrow (\forall (\varepsilon: \mathbb{R}), ((-1 < \varepsilon) \Rightarrow ((\varepsilon < 1) \Rightarrow (\forall (i: \operatorname{Fin}\left(L\right)), (\forall (j: \operatorname{Fin}\left(L\right)), (\frac{\operatorname{p}\left(wp, \varepsilon, i\right)}{\operatorname{q}\left(wm, \varepsilon, i + 1\right)} = \frac{\operatorname{p}\left(wp, \varepsilon, j\right)}{\operatorname{q}\left(wm, \varepsilon, j + 1\right)}))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.BondRatioUniform` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

The bond-bias ratio of equation (5) is p(wp,ε,i)/q(wm,ε,i + 1). Condition (i) in Section III.D requires equality of these ratios for every pair of sites at every bias strictly between −1 and 1.

**Definition 1.7 (Condition (ii): inversion and bias reversal).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)], (\forall (wp: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (wm: \operatorname{Fin}\left(L\right) \to \mathbb{R}), ((\operatorname{InversionCorrespondence}\left(wp, wm\right)) \Leftrightarrow (\exists (k: \operatorname{Fin}\left(L\right)), (\forall (i: \operatorname{Fin}\left(L\right)), ((\forall (\varepsilon: \mathbb{R}), (\operatorname{p}\left(wp, \varepsilon, k + i\right) = \operatorname{q}\left(wm, -\varepsilon, k - i\right))) \lor (\forall (\varepsilon: \mathbb{R}), (\operatorname{p}\left(wp, \varepsilon, k + i\right) = \operatorname{q}\left(wm, -\varepsilon, k - i + 1\right))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.InversionCorrespondence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

Condition (ii) in Section III.D and Appendix C uses one centre k for the whole ring. For each site offset i, either the reflected site k − i or the shifted reflected site k − i + 1 has the matching leftward rate at reversed bias. The choice may depend on i, but each chosen equality must hold for every real ε.

**Definition 1.8 (The proposed nonzero quadratic coefficient).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (L: \mathbb{N}), (\forall (N: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)], ((2 \le N) \Rightarrow ((N + 2 \le L) \Rightarrow (\forall (wp: \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (wm: \operatorname{Fin}\left(L\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(L\right)), ((0 < wp\left(i\right)) \land (0 < wm\left(i\right)))) \Rightarrow ((\prod_{(i: \operatorname{Fin}\left(L\right))} (wm\left(i\right)) = \prod_{(i: \operatorname{Fin}\left(L\right))} (wp\left(i\right))) \Rightarrow ((\neg (\operatorname{BondRatioUniform}\left(wp, wm\right))) \Rightarrow ((\neg (\operatorname{InversionCorrespondence}\left(wp, wm\right))) \Rightarrow (\forall (\delta: \mathbb{R}), ((0 < \delta) \Rightarrow (\forall (\pi: \mathbb{R} \to \left(\operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right) \to \mathbb{R}\right)), ((\forall (\varepsilon: \mathbb{R}), ((\lvert\varepsilon\rvert < \delta) \Rightarrow ((\operatorname{IsStationary}\left(N, wp, wm, \varepsilon, \pi\left(\varepsilon\right)\right)) \land (\forall (\mu: \operatorname{Finset}\left(\operatorname{Fin}\left(L\right)\right) \to \mathbb{R}), ((\operatorname{IsStationary}\left(N, wp, wm, \varepsilon, \mu\right)) \Rightarrow (\mu = \pi\left(\varepsilon\right))))))) \Rightarrow (\forall (c_{1}: \mathbb{R}), (\forall (c_{2}: \mathbb{R}), ((\operatorname{Asymptotics.IsLittleO}\left(\operatorname{nhds}\left((0: \mathbb{R})\right), \lambda (\varepsilon: \mathbb{R}) \mapsto (\operatorname{current}\left(wp, wm, \varepsilon, \pi\left(\varepsilon\right)\right) - c_{1} \cdot \varepsilon - c_{2} \cdot \varepsilon^{2}), \lambda (\varepsilon: \mathbb{R}) \mapsto (\varepsilon^{2})\right)) \Rightarrow (c_{2} \ne 0)))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.claim` (`✓ std3`).

*Citation.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

Section III.D conjectures an ε² contribution whenever neither condition (i) nor condition (ii) holds. Here the statement is restricted to at least two particles and at least two holes; Section III.F already gives an odd current for a single particle. The rates are positive and their two products agree, expressing the unbiased equilibrium constraint of Section II. For every positive δ and every family π that is the unique stationary law for |ε| < δ, every quadratic expansion of its current must have c₂ nonzero. Asymptotics.IsLittleO at nhds(0) means that the remainder is o(ε²) as the real bias tends to zero; the two displayed lambda expressions are functions of that bias.

**Theorem 1.9 (Four trap sites with a zero quadratic coefficient).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sakai-akimoto-2026-disordered-exclusion-quadratic-response` (refuted) by `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sakai-akimoto-2026-disordered-exclusion-quadratic-response","declaration_gid":"D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Issei Sakai; Takuma Akimoto (2026). *Symmetry breaking of current response in disordered exclusion processes*. DOI: [10.1103/21vm-n8gp](https://doi.org/10.1103/21vm-n8gp). URL: <https://arxiv.org/abs/2512.03316v2>.

*Commentary.*

Take L = 4 and N = 2, and give both directions the trap rates (2,4,3,41) at sites 0,1,2,3. The rates are positive and their products agree. At ε = 0, the ratios across the first two bonds are 1/2 and 4/3, so condition (i) fails. For any centre k, the offset i = 1 compares the rate at k + 1 with the rates at k − 1 and k. These three sites are distinct modulo 4 and all four trap rates are distinct. Thus neither alternative is possible at ε = 0, and condition (ii) fails.

For |ε| < 1/100, the stationary probabilities on the ordered configurations ({0,1},{0,2},{0,3},{1,2},{1,3},{2,3}) are the following six entries divided by 5(223175 + 17022ε² − 1628ε³ − 114725ε⁴ + 1628ε⁵): 123(2825 − 1612ε + 390ε² + 1256ε³ − 1695ε⁴ + 148ε⁵), 164(2825 + 518ε − 928ε² − 370ε³ − 1033ε⁴ − 148ε⁵), 12(2825 + 5608ε + 4830ε² + 3036ε³ + 1265ε⁴ + 148ε⁵), 82(2825 + 1008ε + 1150ε² − 1564ε³ − 2415ε⁴ + 148ε⁵), 6(2825 − 222ε + 2672ε² + 370ε³ − 2873ε⁴ − 148ε⁵), and 8(2825 − 4412ε + 2630ε² − 1544ε³ + 545ε⁴ + 148ε⁵). The law is zero on all other configurations. The six numerators sum to the denominator and satisfy the balance equations. They and the denominator are positive on this interval. The balance equations together with total mass one determine these probabilities uniquely.

The resulting bond current is 7872ε(25 + 9ε² − 16ε⁴)/(223175 + 17022ε² − 1628ε³ − 114725ε⁴ + 1628ε⁵). Its linear coefficient is 7872/8927 and its quadratic coefficient is zero: subtracting (7872/8927)ε leaves ε³ times a function continuous at zero, hence a remainder o(ε²). Its ε⁴ coefficient is 7872·25·1628/223175², which is positive, so the current is not odd. The vanishing quadratic term therefore does not require either rate condition and does not imply bias-reversal symmetry.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.BondRatioUniform`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.InversionCorrespondence`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.IsStationary`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.current`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.p`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.q`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.rate`
- Truth anchor: `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.result`
