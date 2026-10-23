# Glauber relaxation times do not order energy relaxation rates

## Abstract

A four-state Glauber annealing run has a larger spectral gap but a smaller energy relaxation rate than a partial swap process.

The finite state space is Fin N. Energies and probabilities are real-valued, and probability vectors are columns. The relation A describes the neighbourhood, while beta is the inverse-temperature schedule. All sums over Fin N include every state. A DecidableRel A supplies a decision for each adjacency statement A i j; the bracketed DecidableRel A is an anonymous typeclass assumption. Natural numbers in real-valued expressions are coerced to the reals.

**Definition 1.1 (A regular undirected neighbourhood).**

$$\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.regularNeighborhood}\left(n, A\right)) \Leftrightarrow ((1 \le n) \land ((\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), ((A\left(i, j\right)) \Rightarrow (A\left(j, i\right))))) \land ((\forall (i: \operatorname{Fin}\left(N\right)), (\neg (A\left(i, i\right)))) \land (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (i: \operatorname{Fin}\left(N\right)) \mapsto (A\left(i, j\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right))\right)\right) = n)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.regularNeighborhood` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Every state has exactly n neighbours, with n at least one. Adjacency is symmetric and irreflexive. Finset.univ is the finite set of all states; Finset.filter retains the states adjacent to j, and Finset.card counts them. This is the equal-sized neighbourhood setting of Eqs. (31) and (78).

**Definition 1.2 (The Gibbs distribution).**

$$\forall (N: \mathbb{N}), (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (b: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, i\right) = \frac{\operatorname{Real.exp}\left((-b) \cdot (E\left(i\right))\right)}{\sum_{(j: \operatorname{Fin}\left(N\right))} (\operatorname{Real.exp}\left((-b) \cdot (E\left(j\right))\right))}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.gibbs` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

The thermal probabilities used in Eq. (32) are normalized Boltzmann weights. Real.exp is the real exponential, and the denominator sums its weights over every state.

**Definition 1.3 (Accepted transitions along edges).**

$$\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (b: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.edgeWeight}\left(n, A, E, b, i, j\right) = \mathrm{if} (A\left(i, j\right)) \mathrm{then} (\frac{\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, i\right)}{((n: \mathbb{R})) \cdot ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, i\right)) + (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, b, j\right)))}) \mathrm{else} (0)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.edgeWeight` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Equations (31) and (32) give the Gibbs-ratio acceptance probability divided by the neighbourhood size n. The entry vanishes when A i j is false. The definition itself imposes no positivity or regularity assumptions.

**Definition 1.4 (The Glauber transition matrix).**

$$\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (b: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.glauber}\left(n, A, E, b, i, j\right) = \mathrm{if} (i = j) \mathrm{then} ((1) - (\sum_{(l: \operatorname{Fin}\left(N\right))} (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.edgeWeight}\left(n, A, E, b, l, j\right)))) \mathrm{else} (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.edgeWeight}\left(n, A, E, b, i, j\right))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.glauber` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

The off-diagonal entries are the accepted edge transitions. Each diagonal entry is one minus the sum of the edge weights in that column over all l, including l = j. For an irreflexive neighbourhood the self-edge weight is zero, so this is Eq. (31).

**Definition 1.5 (Annealing from an initial thermal state).**

$$(\forall (N: \mathbb{N}), (\forall (p: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), ((\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(p\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(N\right)), (0 \le p\left(i\right))) \land (\sum_{(i: \operatorname{Fin}\left(N\right))} (p\left(i\right)) = 1))))) \land (\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (beta: (\mathbb{N} \to \mathbb{R})), (\forall (p: (\mathbb{N} \to (\operatorname{Fin}\left(N\right) \to \mathbb{R}))), ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.isSARun}\left(n, A, E, beta, p\right)) \Leftrightarrow ((\forall (t: \mathbb{N}), (\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(p\left(t\right)\right))) \land ((p\left(0\right) = \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left(0\right)\right)) \land (\forall (t: \mathbb{N}), (p\left((t) + (1)\right) = \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.glauber}\left(n, A, E, beta\left((t) + (1)\right)\right), p\left(t\right)\right)))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.isSARun` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

D5.S3.TotalVariation.CycleSingleCutMinimax.Probability requires nonnegative entries with total mass one, as required for the states in Eq. (30). Every time slice is a probability vector. The initial vector is the Gibbs distribution at beta(0), and Eq. (30) updates p(t) using the transition matrix at beta(t + 1). Matrix.mulVec multiplies a matrix by a column vector: its i-th coordinate is the sum of the matrix entries in row i times the corresponding vector entries. The recursion holds at every natural time.

**Theorem 1.6 (Column-stochastic matrices preserve probability).**

$$\forall (N: \mathbb{N}), (\forall (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right)), (\forall (p: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), ((\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (0 \le P\left(i\right)\left(j\right)))) \Rightarrow ((\forall (j: \operatorname{Fin}\left(N\right)), (\sum_{(i: \operatorname{Fin}\left(N\right))} (P\left(i\right)\left(j\right)) = 1)) \Rightarrow ((\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(p\right)) \Rightarrow (\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(\operatorname{Matrix.mulVec}\left(P, p\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.probability_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

A real matrix with nonnegative entries and every column summing to one sends a probability vector to another probability vector under Matrix.mulVec.

**Definition 1.7 (Mean energy).**

$$\forall (N: \mathbb{N}), (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (p: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\right) = \sum_{(i: \operatorname{Fin}\left(N\right))} ((E\left(i\right)) \cdot (p\left(i\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.meanEnergy` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Mean energy is the sum of each energy level times its probability, as in Eqs. (44) and (46). The expression is defined for any real-valued vector p.

**Definition 1.8 (The energy relaxation rate).**

$$\forall (N: \mathbb{N}), (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (beta: (\mathbb{N} \to \mathbb{R})), (\forall (p: (\mathbb{N} \to (\operatorname{Fin}\left(N\right) \to \mathbb{R}))), (\forall (k: \mathbb{N}), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.energyRate}\left(E, beta, p, k\right) = \frac{(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\left((k) + (1)\right)\right)) - (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\left(k\right)\right))}{(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left((k) + (1)\right)\right)\right)) - (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\left(k\right)\right))})))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.energyRate` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Equation (46) divides the actual energy change at step k by the change needed to reach the Gibbs energy at the next inverse temperature. The conjecture below assumes that this denominator is nonzero.

**Definition 1.9 (The second characteristic root in descending order).**

$$\forall (N: \mathbb{N}), (\forall (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.lambda2}\left(P\right) = \operatorname{List.getD}\left(\operatorname{Multiset.sort}\left(\operatorname{Polynomial.roots}\left(\operatorname{Matrix.charpoly}\left(P\right)\right), \lambda (x: \mathbb{R}) \mapsto (\lambda (y: \mathbb{R}) \mapsto (y \le x))\right), 1, (0: \mathbb{R})\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.lambda2` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Matrix.charpoly P is the characteristic polynomial det(X I - P). Polynomial.roots is its multiset of real roots, with algebraic multiplicity. Multiset.sort lists these roots using the relation y <= x, hence in descending order. List.getD takes the entry at zero-based index 1 and returns the real number zero if that entry is absent. When the characteristic polynomial splits over the reals and N is at least two, this is the second largest eigenvalue counted with multiplicity, as in Eq. (50).

**Definition 1.10 (The relaxation-order conjecture).**

$$(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.claim}) \Leftrightarrow (\forall (N: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (A: (\operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \operatorname{Prop}\right))), ([\operatorname{DecidableRel}\left(A\right)] (\forall (E: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), (\forall (beta: (\mathbb{N} \to \mathbb{R})), (\forall (p: (\mathbb{N} \to (\operatorname{Fin}\left(N\right) \to \mathbb{R}))), (\forall (k: \mathbb{N}), (\forall (m: \mathbb{R}), ((2 \le N) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.regularNeighborhood}\left(n, A\right)) \Rightarrow ((\forall (t: \mathbb{N}), (0 < beta\left(t\right))) \Rightarrow ((\operatorname{StrictMono}\left(beta\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.isSARun}\left(n, A, E, beta, p\right)) \Rightarrow ((\operatorname{Polynomial.Splits}\left(\operatorname{Matrix.charpoly}\left(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.glauber}\left(n, A, E, beta\left((k) + (1)\right)\right)\right)\right)) \Rightarrow ((0 < m) \Rightarrow ((m \le 1) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\left((k) + (1)\right)\right) \le \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\left(k\right)\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left(k\right)\right)\right) \le \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\left(k\right)\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left((k) + (1)\right)\right)\right) \le \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left(k\right)\right)\right)) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, beta\left((k) + (1)\right)\right)\right) \ne \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.meanEnergy}\left(E, p\left(k\right)\right)) \Rightarrow ((m \le (1) - (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.lambda2}\left(\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.glauber}\left(n, A, E, beta\left((k) + (1)\right)\right)\right))) \Rightarrow (m \le \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.energyRate}\left(E, beta, p, k\right))))))))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.claim` (`✓ std3`).

*Citation.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Equation (50) asserts that a relaxation time no greater than that of a partial swap process implies an energy relaxation rate at least as large. Here StrictMono beta means that beta(t) < beta(u) whenever t < u. Polynomial.Splits says that the displayed characteristic polynomial splits into linear factors over the reals. The hypotheses require at least two states, a regular neighbourhood, positive strictly increasing inverse temperatures, the entire annealing run, real splitting, and a partial swap rate 0 < m <= 1. They also require nonincreasing actual energy, actual energy at least the current Gibbs energy, nonincreasing Gibbs energy, and a nonzero energy denominator, in that order. Proposition 2 gives partial swap relaxation time 1/m. With m positive, the final spectral-gap hypothesis ensures that the Glauber relaxation time is finite and at most 1/m. The conclusion is the energy-rate comparison of Eq. (50).

**Theorem 1.11 (A four-state cycle reverses the proposed order).**

$$\neg (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/luo-zhen-liu-ebler-dahlsten-2023-relaxation-order-refutation` (refuted) by `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"luo-zhen-liu-ebler-dahlsten-2023-relaxation-order-refutation","declaration_gid":"D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten (2023). *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*. DOI: [10.1103/PhysRevE.108.054119](https://doi.org/10.1103/PhysRevE.108.054119). URL: <https://arxiv.org/abs/2311.10424v1>.

*Commentary.*

Take the cycle 0-1-2-3-0 with energies (0, 1, 1, 2) and two neighbours per state. Choose the inverse-temperature schedule with Real.exp(beta(t)) = 2 at t = 0 and t + 31 for t > 0, so its successive values are 2, 32, 33, 34, and so on. Start in the Gibbs state and apply the Glauber updates. At the second step, k = 1, the energy relaxation rate is 2673903/17337104, and the second characteristic root is 1/2 + Real.sqrt(64/545). All the energy and spectral hypotheses hold, while the partial swap rate m = 5/32 is strictly below the Glauber spectral gap and strictly above the energy relaxation rate. Thus the implication in Eq. (50) fails.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.edgeWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.energyRate`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.gibbs`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.glauber`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.isSARun`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.lambda2`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.meanEnergy`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.probability_mulVec`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.regularNeighborhood`
- Truth anchor: `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.result`
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../TotalVariation/CycleSingleCutMinimax.md)
