# A self-dual factorization of an irreducible thermal process

## Abstract

A five-level self-dual irreducible extreme thermal process factors into two extreme processes acting on fewer levels, refuting the non-self-duality conjecture.

**Definition 1.1 (Thermal processes).**

$$\forall d \in \mathbb{N},\; (\forall g \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\; ((T \in \operatorname{thermalProcesses}\left(g\right)) \Leftrightarrow ((T \in \operatorname{Matrix}.\operatorname{colStochastic}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right)) \land (\operatorname{Matrix}.\operatorname{mulVec}\left(T, g\right) = g)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.thermalProcesses` (`✓ std3`).

*Citation.* Paweł Mazurek; Michał Horodecki (2018). *Decomposability and convex structure of thermal processes*. DOI: [10.1088/1367-2630/aac057](https://doi.org/10.1088/1367-2630/aac057). URL: <https://arxiv.org/abs/1707.06869v2>.

*Commentary.*

For a natural dimension d and a real Gibbs vector g on Fin d, a thermal process is a matrix T whose columns are stochastic and which preserves g. This is the Gibbs-preserving column-stochastic characterization stated in the source paper.

**Definition 1.2 (Processes acting on fewer levels).**

$$\forall d \in \mathbb{N},\; (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\; ((\operatorname{actsOnFewerLevels}\left(T\right)) \Leftrightarrow (\exists k \in \operatorname{Fin}\left(d\right),\; (T\left(k, k\right) = 1))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.actsOnFewerLevels` (`✓ std3`).

*Citation.* Paweł Mazurek; Michał Horodecki (2018). *Decomposability and convex structure of thermal processes*. DOI: [10.1088/1367-2630/aac057](https://doi.org/10.1088/1367-2630/aac057). URL: <https://arxiv.org/abs/1707.06869v2>.

*Commentary.*

A process acts non-trivially on at most d minus one levels when it fixes at least one level k, expressed by the diagonal entry T k k being one. This is the source paper's condition for a process acting on a proper subspace.

**Definition 1.3 (Self-duality).**

$$\forall d \in \mathbb{N},\; (\forall g \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\; ((\operatorname{selfDual}\left(g, T\right)) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(d\right),\; (\forall j \in \operatorname{Fin}\left(d\right),\; (T\left(i, j\right) \cdot g\left(j\right) = T\left(j, i\right) \cdot g\left(i\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.selfDual` (`✓ std3`).

*Citation.* Paweł Mazurek; Michał Horodecki (2018). *Decomposability and convex structure of thermal processes*. DOI: [10.1088/1367-2630/aac057](https://doi.org/10.1088/1367-2630/aac057). URL: <https://arxiv.org/abs/1707.06869v2>.

*Commentary.*

Self-duality with respect to the Gibbs weights is the detailed-balance relation T i j times g j equals T j i times g i for every pair of levels. It is equivalent to equality with the conjugated transpose in the source paper.

**Definition 1.4 (Irreducibility).**

$$\forall d \in \mathbb{N},\; (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\; ((\operatorname{irreducible}\left(T\right)) \Leftrightarrow (\neg (\exists S \in \operatorname{Finset}\left(\operatorname{Fin}\left(d\right)\right),\; ((\operatorname{Finset}.\operatorname{Nonempty}\left(S\right)) \land ((\operatorname{Finset}.\operatorname{Nonempty}\left(S^{c}\right)) \land (\forall i \in \operatorname{Fin}\left(d\right),\; (\forall j \in \operatorname{Fin}\left(d\right),\; ((((i \in S) \land (\neg (j \in S))) \lor ((\neg (i \in S)) \land (j \in S))) \Rightarrow (T\left(i, j\right) = 0))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.irreducible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paweł Mazurek; Michał Horodecki (2018). *Decomposability and convex structure of thermal processes*. DOI: [10.1088/1367-2630/aac057](https://doi.org/10.1088/1367-2630/aac057). URL: <https://arxiv.org/abs/1707.06869v2>.

*Commentary.*

Irreducibility reads the phrase not a direct sum as the absence of a nonempty proper set S whose two sides have all cross-block entries zero. Here Sᶜ denotes the complement in the finite level set Fin d.

**Definition 1.5 (The non-self-duality conjecture).**

$$(claim) \Leftrightarrow (\forall d \in \mathbb{N},\; ((2 \le d) \Rightarrow (\forall g \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; ((\forall i \in \operatorname{Fin}\left(d\right),\; (0 < g\left(i\right))) \Rightarrow ((\operatorname{Function}.\operatorname{Injective}\left(g\right)) \Rightarrow ((\forall i \in \operatorname{Fin}\left(d\right),\; (g\left(i\right) \le g\left((0:\operatorname{Fin}\left(d\right))\right))) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\; (\forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\; (\forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\; ((A \in \operatorname{Set}.\operatorname{extremePoints}\left(\mathbb{R}, \operatorname{thermalProcesses}\left(g\right)\right)) \Rightarrow ((B \in \operatorname{Set}.\operatorname{extremePoints}\left(\mathbb{R}, \operatorname{thermalProcesses}\left(g\right)\right)) \Rightarrow ((C \in \operatorname{Set}.\operatorname{extremePoints}\left(\mathbb{R}, \operatorname{thermalProcesses}\left(g\right)\right)) \Rightarrow ((C = A \cdot B) \Rightarrow ((\operatorname{actsOnFewerLevels}\left(A\right)) \Rightarrow ((\operatorname{actsOnFewerLevels}\left(B\right)) \Rightarrow ((\operatorname{irreducible}\left(C\right)) \Rightarrow (\neg (\operatorname{selfDual}\left(g, C\right)))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.claim` (`✓ std3`).

*Citation.* Paweł Mazurek; Michał Horodecki (2018). *Decomposability and convex structure of thermal processes*. DOI: [10.1088/1367-2630/aac057](https://doi.org/10.1088/1367-2630/aac057). URL: <https://arxiv.org/abs/1707.06869v2>.

*Commentary.*

The source conjectures that an extremal thermal process C on d levels, factored as C = A B with extremal factors each fixing a level, cannot be self-dual when C has no direct-sum decomposition across a nonempty proper set of levels. The formal statement assumes d is at least two, all Gibbs weights are positive and pairwise distinct, and the weight at level zero is maximal.

**Theorem 1.6 (A five-level refutation).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mazurek-horodecki-2018-thermal-process-self-dual-factorization-refutation` (refuted) by `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mazurek-horodecki-2018-thermal-process-self-dual-factorization-refutation","declaration_gid":"D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paweł Mazurek; Michał Horodecki (2018). *Decomposability and convex structure of thermal processes*. DOI: [10.1088/1367-2630/aac057](https://doi.org/10.1088/1367-2630/aac057). URL: <https://arxiv.org/abs/1707.06869v2>.

*Commentary.*

Set d = 5 and use the Gibbs weights (8, 7, 4, 2, 3). Let A be the matrix with rows (0, 1, 0, 1/2, 0), (1/4, 0, 1, 1/2, 0), (1/2, 0, 0, 0, 0), (1/4, 0, 0, 0, 0), (0, 0, 0, 0, 1); it acts on levels 0 through 3 and fixes level 4. Let B have rows (1, 0, 0, 0, 0), (0, 1/7, 1, 1, 0), (0, 1/7, 0, 0, 1), (0, 2/7, 0, 0, 0), (0, 3/7, 0, 0, 0), so it fixes level 0. Their product is C = A B, with rows (0, 2/7, 1, 1, 0), (1/4, 2/7, 0, 0, 1), (1/2, 0, 0, 0, 0), (1/4, 0, 0, 0, 0), (0, 3/7, 0, 0, 0). Each of A, B and C is nonnegative, column-stochastic and preserves the Gibbs weights. Each is extreme by support uniqueness: in a convex combination, every factor has zero entries wherever the matrix has a zero entry, and the column sums together with Gibbs preservation determine all remaining entries uniquely. The non-loop support edges of C are 0–1, 0–2, 0–3 and 1–4, so C is irreducible. Finally, C satisfies detailed balance: C times the diagonal matrix of the Gibbs weights is symmetric. Thus the factorization satisfies every hypothesis of claim while its conclusion fails.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.actsOnFewerLevels`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.irreducible`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.selfDual`
- Truth anchor: `D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.thermalProcesses`
