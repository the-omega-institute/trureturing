# Neighbourhood passivity is not preserved by Glauber annealing

## Abstract

A Petersen-graph Glauber annealing run violates neighbourhood passivity.

The finite state space is Fin N. Energies, inverse temperatures and populations are real-valued, and populations are columns. The relation A describes a regular neighbourhood, while beta is the inverse-temperature schedule. All sums over Fin N include every state; a sum indexed by membership in a filtered Finset ranges over exactly the displayed neighbours. The bracketed DecidableRel A is an anonymous instance argument.

**Definition 1.1 (Neighbourhood passivity at the next temperature).**

$$\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (beta: (\mathbb{N} \to \mathbb{R})), (\forall (p: (\mathbb{N} \to (\operatorname{Fin}\left(N\right) \to \mathbb{R}))), (\forall (k: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberNeighbourhoodPassivityRefutation.neighbourhoodPassivity}\left(n, A, E, beta, p, k, i\right) = \sum_{j \in \operatorname{Finset.filter}\left(\lambda (j: \operatorname{Fin}\left(N\right)) \mapsto (A\left(i, j\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right))\right)} ((\frac{(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left((k) + (1)\right), i\right)) - \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left((k) + (1)\right), j\right)}{(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left((k) + (1)\right), i\right)) + (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left((k) + (1)\right), j\right))}) \cdot ((p\left(k, i\right)) - p\left(k, j\right))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.neighbourhoodPassivity` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

For state i at step k, the Gibbs weights are evaluated at beta(k + 1), while the population differences use p(k). The sum runs over the states adjacent to i and is the ratio-weighted passivity expression in Eq. (41). The five reused annealing definitions are displayed below.

$$
\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.regularNeighborhood}\left(n, A\right)) \Leftrightarrow ((1 \le n) \land ((\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), ((A\left(i, j\right)) \Rightarrow (A\left(j, i\right))))) \land ((\forall (i: \operatorname{Fin}\left(N\right)), (\neg (A\left(i, i\right)))) \land (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (i: \operatorname{Fin}\left(N\right)) \mapsto (A\left(i, j\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right))\right)\right) = n)))))))))
$$

$$
\forall (N: \mathbb{N}), (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (b: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, i\right) = \frac{\operatorname{Real.exp}\left((-b) \cdot (E\left(i\right))\right)}{\sum_{(j: \operatorname{Fin}\left(N\right))} (\operatorname{Real.exp}\left((-b) \cdot (E\left(j\right))\right))}))))
$$

$$
\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (b: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.edgeWeight}\left(n, A, E, b, i, j\right) = \mathrm{if} (A\left(i, j\right)) \mathrm{then} (\frac{\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, i\right)}{((n: \mathbb{R})) \cdot ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, i\right)) + (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, j\right)))}) \mathrm{else} (0)))))))))
$$

$$
\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (b: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.glauber}\left(n, A, E, b, i, j\right) = \mathrm{if} (i = j) \mathrm{then} ((1) - \sum_{(l: \operatorname{Fin}\left(N\right))} (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.edgeWeight}\left(n, A, E, b, l, j\right))) \mathrm{else} (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.edgeWeight}\left(n, A, E, b, i, j\right))))))))))
$$

$$
(\forall (N: \mathbb{N}), (\forall (p: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), ((\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(p\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(N\right)), (0 \le p\left(i\right))) \land (\sum_{(i: \operatorname{Fin}\left(N\right))} (p\left(i\right)) = 1))))) \land (\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (beta: (\mathbb{N} \to \mathbb{R})), (\forall (p: (\mathbb{N} \to (\operatorname{Fin}\left(N\right) \to \mathbb{R}))), ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.isSARun}\left(n, A, E, beta, p\right)) \Leftrightarrow ((\forall (t: \mathbb{N}), (\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(p\left(t\right)\right))) \land ((p\left(0\right) = \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left(0\right)\right)) \land (\forall (t: \mathbb{N}), (p\left((t) + (1)\right) = \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.glauber}\left(n, A, E, beta\left((t) + (1)\right)\right), p\left(t\right)\right)))))))))))))
$$

**Definition 1.2 (The neighbourhood-passivity expectation).**

$$(\operatorname{D5.S3.StatisticalMechanics.GlauberNeighbourhoodPassivityRefutation.claim}) \Leftrightarrow (\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (beta: (\mathbb{N} \to \mathbb{R})), (\forall (p: (\mathbb{N} \to (\operatorname{Fin}\left(N\right) \to \mathbb{R}))), ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.regularNeighborhood}\left(n, A\right)) \Rightarrow ((\operatorname{SimpleGraph.Connected}\left(\operatorname{SimpleGraph.fromRel}\left(A\right)\right)) \Rightarrow ((\operatorname{Function.Injective}\left(E\right)) \Rightarrow ((\operatorname{StrictMono}\left(beta\right)) \Rightarrow ((0 < beta\left(0\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.isSARun}\left(n, A, E, beta, p\right)) \Rightarrow (\forall (k: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(N\right)), (0 \le \operatorname{D5.S3.StatisticalMechanics.GlauberNeighbourhoodPassivityRefutation.neighbourhoodPassivity}\left(n, A, E, beta, p, k, i\right)))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.claim` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

The source expects every connected regular neighbourhood with distinct energies to preserve nonnegative neighbourhood passivity throughout a Glauber annealing run started in the Gibbs state. The schedule is strictly increasing and starts at a positive inverse temperature. The conclusion quantifies over every step and every state.

**Theorem 1.3 (A Petersen graph gives negative neighbourhood passivity).**

$$\neg (\operatorname{D5.S3.StatisticalMechanics.GlauberNeighbourhoodPassivityRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/luo-zhen-liu-ebler-dahlsten-2023-neighbourhood-passivity-refutation` (refuted) by `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"luo-zhen-liu-ebler-dahlsten-2023-neighbourhood-passivity-refutation","declaration_gid":"D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Use the Petersen graph on ten states. Its neighbour sets, in order from 0 through 9, are {1,4,5}, {0,2,6}, {1,3,7}, {2,4,8}, {0,3,9}, {0,7,8}, {1,8,9}, {2,5,9}, {3,5,6}, and {4,6,7}. Every state has three neighbours, the relation is symmetric and irreflexive, and the graph is connected.

The energy vector on states 0 through 9 is (3,4,6,7,5,2,8,0,1,9). The inverse-temperature schedule is beta(0) = log(11/10) and beta(k) = log(4k) for every k at least 1; the first three values used here are log(11/10), log 4, and log 8. Start with the Gibbs population at log(11/10) and apply the Glauber matrix at the next scheduled temperature.

The exact first population is (6495040420/47812273803, 1579228369400/12287754367371, 531822026923/11522757986523, 160582769930/11522757986523, 442180927000/4095918122457, 4048016885/47812273803, 49100916611546/1388516243512923, 2707415959783376/11662677190645065, 268789869032696/1302071652477099, 782236372623151/87058739692823535). It is obtained by one exact matrix-vector multiplication.

At step 1 and state 0, the three neighbours have energies 4, 5 and 2. At beta(2) = log 8, the corresponding Gibbs-ratio weights are 7/9, 63/65 and −7/9. Substitution of the exact first population gives P_0(1) = −1454086156987/205381037283201, which is negative. Thus the universal nonnegativity assertion fails.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.neighbourhoodPassivity`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.result`
- Dependency: [D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation](GlauberRelaxationOrderRefutation.md)
