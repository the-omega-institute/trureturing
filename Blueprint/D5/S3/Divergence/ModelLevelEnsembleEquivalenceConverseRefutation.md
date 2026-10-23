# Model-level equivalence does not imply measure-level equivalence

## Abstract

A scalar statistic with bounded dyadic weights on binary square matrices separates model-level and measure-level ensemble equivalence.

Giuffrida, Squartini, Grünwald and Garlaschelli, arXiv:2307.05645v4, Section III, p. 4: “Specifically, we will focus on discrete data that can be represented as a binary n × m matrix G, i.e.” Here m = n. Both indices range over Fin n and Bool represents the entries zero and one. All displayed sums range over the whole indicated finite type. Natural cardinalities and n in real quotients are coerced to the reals. Real division has its Lean total meaning at zero; only eventual positive sizes enter the limits.

**Definition 1.1 (The size of a statistic fiber).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (c: \mathbb{R}), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.omega}\left(stat, c\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \mapsto (stat\left(G\right) = c), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))\right))\right)\right))))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.omega` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section III, p. 4: “Ω(c) denotes the number of configurations with c(G) = c, i.e.,” followed by equation (15), which counts all binary matrices whose scalar statistic is c. Finset.filter selects that fiber from Finset.univ and Finset.card counts it.

**Definition 1.2 (The microcanonical law).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (c: \mathbb{R}), (\forall (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.pMic}\left(stat, c, G\right) = \operatorname{if} (stat\left(G\right) = c) \operatorname{then} \frac{1}{(\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.omega}\left(stat, c\right): \mathbb{R})} \operatorname{else} 0))))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.pMic` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section III.A, p. 4: “When considering microcanonical models, entropy maximization yields the following functional form” followed by equation (16). It is the uniform law on the selected fiber and zero outside it.

**Definition 1.3 (Expectation matching).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (theta: \mathbb{R}), (\forall (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))), ((\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.IsMatched}\left(stat, theta, G\right)) \Leftrightarrow (\sum_{(K: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))} ((\frac{\operatorname{Real.exp}\left((-theta) \cdot (stat\left(K\right))\right)}{\sum_{(H: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))} (\operatorname{Real.exp}\left((-theta) \cdot (stat\left(H\right))\right))}) \cdot (stat\left(K\right))) = stat\left(G\right))))))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.IsMatched` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section III, p. 4: “The ML estimators θ̂(G) are found by solving the system of equations” followed by equation (21). The equation equates the canonical expectation of the statistic to stat G. On the same page: “When considering canonical models, entropy maximization yields the following well-known exponential form” followed by equation (20). The canonical weights are these normalized exponentials.

**Definition 1.4 (Measure-level divergence).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))), (\forall (theta: \mathbb{R}), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.measureDiv}\left(stat, G, theta\right) = \operatorname{D5.S3.Divergence.ClassicalDPI.klDivergence}\left(\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.pMic}\left(stat, stat\left(G\right)\right), \lambda (K: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \mapsto (\frac{\operatorname{Real.exp}\left((-theta) \cdot (stat\left(K\right))\right)}{\sum_{(H: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))} (\operatorname{Real.exp}\left((-theta) \cdot (stat\left(H\right))\right))})\right)))))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.measureDiv` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section III.B, p. 5: “The maximum log-likelihood of a canonical model is linked to the microcanonical one through the Kullback-Leibler divergence:” followed by equation (22). This is the divergence from the microcanonical law at stat G to the canonical law at theta. At expectation-matched theta this is the source's measure divergence. ClassicalDPI.klDivergence is the real finite sum of a times Real.log(a/b).

**Definition 1.5 (Maximized microcanonical likelihood).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.lMic}\left(stat, G\right) = \frac{1}{(\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.omega}\left(stat, stat\left(G\right)\right): \mathbb{R})})))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.lMic` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section III.A, p. 4: “Its maximum log-likelihood simply reads” followed by equation (17). Exponentiating assigns the reciprocal size of the observed statistic's fiber.

**Definition 1.6 (Maximized canonical likelihood).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.lCan}\left(stat, G\right) = \operatorname{iSup}\left(\lambda (theta: \mathbb{R}) \mapsto (\frac{\operatorname{Real.exp}\left((-theta) \cdot (stat\left(G\right))\right)}{\sum_{(H: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))} (\operatorname{Real.exp}\left((-theta) \cdot (stat\left(H\right))\right))})\right))))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.lCan` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section II, p. 3: “with θ̂(x) being the maximum-likelihood (ML) estimator of θ, i.e.” followed by equation (5). The canonical likelihood is maximized over every real theta. The supremum also includes limiting values approached at extreme statistic fibers.

**Definition 1.7 (Microcanonical normalized maximum likelihood).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.nmlMic}\left(stat, G\right) = \frac{\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.lMic}\left(stat, G\right)}{\sum_{(H: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))} (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.lMic}\left(stat, H\right))})))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.nmlMic` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section II, p. 3: “The unique solution to this minimax problem reads” followed by equation (8), “which is a normalized maximum likelihood.” It divides the maximized likelihood by its sum over every possible data matrix.

**Definition 1.8 (Canonical normalized maximum likelihood).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (G: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.nmlCan}\left(stat, G\right) = \frac{\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.lCan}\left(stat, G\right)}{\sum_{(H: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))} (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.lCan}\left(stat, H\right))})))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.nmlCan` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section II, p. 3: “The unique solution to this minimax problem reads” followed by equation (8), “which is a normalized maximum likelihood.” The canonical model uses the same likelihood-over-sum formula.

**Definition 1.9 (Model-level divergence).**

$$\forall (n: \mathbb{N}), (\forall (stat: ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.modelDiv}\left(stat\right) = \operatorname{D5.S3.Divergence.ClassicalDPI.klDivergence}\left(\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.nmlMic}\left(stat\right), \operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.nmlCan}\left(stat\right)\right)))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.modelDiv` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section IV.C, p. 9: “Inspired by the measure level definition of non-equivalence [18] of equation (35), we consider the following KL divergence” followed by equation (69). It compares the two normalized maximum-likelihood distributions using the real finite Kullback–Leibler divergence.

**Definition 1.10 (The converse of model-level ensemble equivalence).**

$$(\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.claim}) \Leftrightarrow (\forall (stat: (\forall (n: \mathbb{N}), ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R}))), ((\operatorname{Filter.Tendsto}\left(\lambda (n: \mathbb{N}) \mapsto (\frac{\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.modelDiv}\left(stat\left(n\right)\right)}{(n: \mathbb{R})}), \operatorname{Filter.atTop}, \operatorname{nhds}\left((0: \mathbb{R})\right)\right)) \Rightarrow (\forall (obs: (\forall (n: \mathbb{N}), (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))), (\forall (theta: (\mathbb{N}) \to (\mathbb{R})), ((\operatorname{Filter.Eventually}\left(\lambda (n: \mathbb{N}) \mapsto (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.IsMatched}\left(stat\left(n\right), theta\left(n\right), obs\left(n\right)\right)), \operatorname{Filter.atTop}\right)) \Rightarrow (\operatorname{Filter.Tendsto}\left(\lambda (n: \mathbb{N}) \mapsto (\frac{\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.measureDiv}\left(stat\left(n\right), obs\left(n\right), theta\left(n\right)\right)}{(n: \mathbb{R})}), \operatorname{Filter.atTop}, \operatorname{nhds}\left((0: \mathbb{R})\right)\right)))))))$$

*Formalization.* `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.claim` (`✓ std3`).

*Citation.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Section IV.C, p. 9, following (71), verbatim: “i.e., whenever ensemble equivalence holds, the corresponding microcanonical and canonical models are equivalent on the model level. The reverse implication, verified here in the specific case of one-sided local constraints, will be investigated in future work.” The proposition is that converse, restricted to scalar statistics on binary n × n matrices and to observation sequences with an eventually finite expectation-matching real parameter. Tendsto uses Filter.atTop on natural sizes and nhds 0 on the reals, with scale n as in (35) and (70).

**Theorem 1.11 (A scalar family refutes the converse).**

$$\neg (\forall (stat: (\forall (n: \mathbb{N}), ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}))) \to (\mathbb{R}))), ((\operatorname{Filter.Tendsto}\left(\lambda (n: \mathbb{N}) \mapsto (\frac{\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.modelDiv}\left(stat\left(n\right)\right)}{(n: \mathbb{R})}), \operatorname{Filter.atTop}, \operatorname{nhds}\left((0: \mathbb{R})\right)\right)) \Rightarrow (\forall (obs: (\forall (n: \mathbb{N}), (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})))), (\forall (theta: (\mathbb{N}) \to (\mathbb{R})), ((\operatorname{Filter.Eventually}\left(\lambda (n: \mathbb{N}) \mapsto (\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.IsMatched}\left(stat\left(n\right), theta\left(n\right), obs\left(n\right)\right)), \operatorname{Filter.atTop}\right)) \Rightarrow (\operatorname{Filter.Tendsto}\left(\lambda (n: \mathbb{N}) \mapsto (\frac{\operatorname{D5.S3.Divergence.ModelLevelEnsembleEquivalenceConverseRefutation.measureDiv}\left(stat\left(n\right), obs\left(n\right), theta\left(n\right)\right)}{(n: \mathbb{R})}), \operatorname{Filter.atTop}, \operatorname{nhds}\left((0: \mathbb{R})\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/giuffrida-squartini-grunwald-garlaschelli-2023-ensemble-equivalence-converse` (refuted) by `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"giuffrida-squartini-grunwald-garlaschelli-2023-ensemble-equivalence-converse","declaration_gid":"D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* F. Giuffrida, T. Squartini, P. Grünwald and D. Garlaschelli (2025). *Description length of canonical and microcanonical models*. DOI: [10.1103/1sd2-rxmy](https://doi.org/10.1103/1sd2-rxmy). URL: <https://arxiv.org/abs/2307.05645v4>.

*Commentary.*

Use the first-column statistic obtained by summing (1 + 2^(−i−1)) times the zero-one entry at row i. Its finite dyadic part lies in [0,1), and its integer part is the number of ones. Distinct first columns have distinct statistic values, so all matrix fibers have the same size. For an ordered finite list of energies, the canonical mass at rank k is at most 1/(k+1) for nonnegative theta and at most 1/(N−k) for nonpositive theta. A harmonic-sum bound then gives model divergence between zero and Real.log(4(n+1)²), whose quotient by n tends to zero. For checkerboard observations at even size n = 2m, factorization over bits bounds canonical first-column probability by 2^(−m) for every theta. Measure divergence divided by n is therefore at least Real.log(2)/2. Continuity and the two extreme-energy limits supply a finite expectation-matching theta for every n at least two. This contradicts the proposed converse. The result leaves the source's one-sided local-constraint equivalence intact.

## References

- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.IsMatched`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.claim`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.lCan`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.lMic`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.measureDiv`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.modelDiv`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.nmlCan`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.nmlMic`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.omega`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.pMic`
- Truth anchor: `D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation](../Combinatorics/Graph/DomiRankEntropyRefutation.md)
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](GrandmotherTheorem.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation](../StatisticalMechanics/GlauberRelaxationOrderRefutation.md)
