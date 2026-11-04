# Equal coherence roofs on a mixed rank-two state

## Abstract

A rank-two state in four dimensions has equal coherence roofs, refuting the universal strict-gap claim.

**Definition 1.1 (Symmetric concave coherence functions).**

$$\forall (n: \mathbb{N}), (\forall (f: ((\operatorname{Fin}\left(n\right)) \to (\mathbb{R})) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.IsCoherenceFunction}\left(f\right)) \Leftrightarrow ((\operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{stdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right), f\right)) \land ((\forall (\sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), (\forall (p: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), ((p \in \operatorname{stdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)) \Rightarrow (f\left(p \circ (\sigma: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(n\right)))\right) = f\left(p\right))))) \land (\forall (i: \operatorname{Fin}\left(n\right)), (f\left(\operatorname{Pi.single}\left(i, (1: \mathbb{R})\right)\right) = (0: \mathbb{R})))))))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.IsCoherenceFunction` (`✓ std3`).

*Citation.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

A coherence function is real-valued on the finite probability simplex, concave there, invariant under every coordinate permutation, and zero on every simplex vertex.

**Definition 1.2 (The coherence vector).**

$$\forall (n: \mathbb{N}), (\forall (\psi: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), (\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.coherenceVector}\left(\psi\right) = \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Complex.normSq}\left(\psi\left(i\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.coherenceVector` (`✓ std3`).

*Citation.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

The coherence vector records the squared complex amplitudes in the fixed reference basis by applying Complex.normSq coordinatewise.

**Definition 1.3 (Finite pure-state decompositions).**

$$\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (k: \mathbb{N}), (\forall (p: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\forall (\psi: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\mathbb{C}))), ((\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.IsDecomposition}\left(\rho, k, p, \psi\right)) \Leftrightarrow ((\forall (j: \operatorname{Fin}\left(k\right)), (0 \le p\left(j\right))) \land ((\sum_{j: \operatorname{Fin}\left(k\right)} (p\left(j\right)) = (1: \mathbb{R})) \land ((\forall (j: \operatorname{Fin}\left(k\right)), (\sum_{i: \operatorname{Fin}\left(n\right)} (\operatorname{Complex.normSq}\left(\psi\left(j\right)\left(i\right)\right)) = (1: \mathbb{R}))) \land (\rho = \sum_{j: \operatorname{Fin}\left(k\right)} (((p\left(j\right): \mathbb{C})) \cdot (\operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\psi\left(j\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.IsDecomposition` (`✓ std3`).

*Citation.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

A decomposition consists of nonnegative real weights summing to one, unit-norm complex vectors, and the exact density-matrix sum of their rank-one projectors. Each real weight is embedded into the complex matrix space before scalar multiplication.

**Definition 1.4 (Values of decomposition averages).**

$$\forall (n: \mathbb{N}), (\forall (f: ((\operatorname{Fin}\left(n\right)) \to (\mathbb{R})) \to (\mathbb{R})), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.decompositionValues}\left(f, \rho\right) = \{x: \mathbb{R} \mid \exists (k: \mathbb{N}), (\exists (p: (\operatorname{Fin}\left(k\right)) \to (\mathbb{R})), (\exists (\psi: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\mathbb{C}))), ((\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.IsDecomposition}\left(\rho, k, p, \psi\right)) \land (x = \sum_{j: \operatorname{Fin}\left(k\right)} ((p\left(j\right)) \cdot (f\left(\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.coherenceVector}\left(\psi\left(j\right)\right)\right)))))))\})))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.decompositionValues` (`✓ std3`).

*Citation.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

The value set contains each real average obtained from a finite pure-state decomposition, evaluating the coherence function on every coherence vector.

**Definition 1.5 (The convex roof).**

$$\forall (n: \mathbb{N}), (\forall (f: ((\operatorname{Fin}\left(n\right)) \to (\mathbb{R})) \to (\mathbb{R})), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.convexRoof}\left(f, \rho\right) = \operatorname{sInf}\left(\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.decompositionValues}\left(f, \rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.convexRoof` (`✓ std3`).

*Citation.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

The convex roof is the real infimum of the decomposition-average value set.

**Definition 1.6 (The coherence of assistance).**

$$\forall (n: \mathbb{N}), (\forall (f: ((\operatorname{Fin}\left(n\right)) \to (\mathbb{R})) \to (\mathbb{R})), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.assistance}\left(f, \rho\right) = \operatorname{sSup}\left(\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.decompositionValues}\left(f, \rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.assistance` (`✓ std3`).

*Citation.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

The coherence of assistance is the real supremum of the same decomposition-average value set.

**Definition 1.7 (Mixed density matrices).**

$$\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.IsMixed}\left(\rho\right)) \Leftrightarrow ((\operatorname{Matrix.PosSemidef}\left(\rho\right)) \land ((\operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C})) \land (\operatorname{Matrix.trace}\left((\rho) \cdot (\rho)\right) \ne (1: \mathbb{C}))))))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.IsMixed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

A matrix is mixed when it is positive semidefinite, has complex trace one, and its squared matrix has trace different from one.

**Definition 1.8 (The universal strict roof gap).**

$$(\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (f: ((\operatorname{Fin}\left(n\right)) \to (\mathbb{R})) \to (\mathbb{R})), ((\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.IsCoherenceFunction}\left(f\right)) \Rightarrow ((\exists (p: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), ((p \in \operatorname{stdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)) \land (f\left(p\right) \ne 0))) \Rightarrow (\forall (\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.IsMixed}\left(\rho\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.convexRoof}\left(f, \rho\right) < \operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.assistance}\left(f, \rho\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

The claim asks whether every natural dimension, every symmetric concave coherence function with a nonzero simplex value, and every mixed density matrix have strictly separated convex and assisted roofs.

**Theorem 1.9 (A rank-two counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhao-pereira-ma-fei-2021-coherence-assistance-roof-equality` (refuted) by `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhao-pereira-ma-fei-2021-coherence-assistance-roof-equality","declaration_gid":"D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei (2021). *Coherence of assistance and assisted maximally coherent states*. DOI: [10.1038/s41598-021-85273-8](https://doi.org/10.1038/s41598-021-85273-8). URL: <https://arxiv.org/abs/2103.08818v1>.

*Commentary.*

Choose the quadratic function q(p) = 1 − Σᵢ pᵢ² in dimension four. It is concave on the simplex, permutation invariant, zero at every vertex, and nonzero at the barycenter. Let v = (1/√2, 1/√6, 1/√6, 1/√6) and w = (0, 1/√3, ω/√3, ω²/√3), where ω = (−1 + i√3)/2. Direct calculation gives unit norms and zero mutual inner products. Let P be the sum of their rank-one density matrices and let ρ = (1/2)P. The two vectors make P a self-adjoint idempotent, and the complementary projection has zero trace against ρ. For every complex a and b, the fourth-moment identity Σᵢ |a vᵢ + b wᵢ|⁴ = (|a|² + |b|²)²/3 holds. Therefore every unit vector in the range of P has q equal to 2/3. Positivity of the complementary projection and the zero trace force every positive-weight vector in any decomposition of ρ into the range of P. Hence every decomposition average is 2/3. The displayed two-vector decomposition shows that this value is attained, so the decomposition-value set is exactly {2/3}. Finally ρ is positive semidefinite, has trace one, and has trace(ρ²) = 1/2, so it is mixed. The convex roof and the coherence of assistance are both 2/3, contradicting the strict inequality asserted by the claim.

## References

- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.IsCoherenceFunction`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.IsDecomposition`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.IsMixed`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.assistance`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.claim`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.coherenceVector`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.convexRoof`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.decompositionValues`
- Truth anchor: `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.result`
- Dependency: [D5/S3/Divergence/CoherenceL1RelativeEntropyBound](../../Divergence/CoherenceL1RelativeEntropyBound.md)
- Dependency: [D5/S3/Quantum/Measurement/AntidistinguishabilityGram](../Measurement/AntidistinguishabilityGram.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
