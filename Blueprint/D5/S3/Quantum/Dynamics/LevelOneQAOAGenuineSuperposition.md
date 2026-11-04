# A genuine four-state superposition from level-one QAOA

## Abstract

Level-one QAOA on three qubits reaches a genuine superposition of exactly four computational basis states.

**Definition 1.1 (The transverse-field mixer).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.mixer}\left(n\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}), (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}), \mathbb{C}\right)) = \sum_{(i: \operatorname{Fin}\left(n\right))} (\operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \operatorname{Equiv.piCongrRight}\left(\operatorname{Function.update}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Equiv.refl}\left(\operatorname{Bool}\right)\right), i, \operatorname{Equiv.boolNot}\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.mixer` (`✓ std3`).

*Citation.* Michael Streif; Martin Leib (2020). *Forbidden subspaces for level-1 quantum approximate optimization algorithm and instantaneous quantum polynomial circuits*. DOI: [10.1103/PhysRevA.102.042416](https://doi.org/10.1103/PhysRevA.102.042416). URL: <https://arxiv.org/abs/2007.13563v1>.

*Commentary.*

The mixer is the sum, over all qubits, of the permutation matrices that flip that qubit and leave the others fixed. Each summand is a single-qubit Pauli-X operator on the computational basis Fin n → Bool. This is the mixing Hamiltonian in main.tex, lines 104–105, of the source.

**Definition 1.2 (One phase layer and one mixing layer).**

$$\forall (n: \mathbb{N}), (\forall (e: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})) \to (\mathbb{R})), (\forall (\beta: \mathbb{R}), (\forall (\gamma: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.qaoaState}\left(n, e, \beta, \gamma\right): ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})) \to (\mathbb{C})) = \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.mixer}\left(n\right), \beta\right), \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator}\left(\operatorname{Matrix.diagonal}\left(\lambda (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})) \mapsto (\operatorname{Complex.ofReal}\left(e\left(x\right)\right))\right), \gamma\right), \operatorname{D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.plusState}\left(n\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.qaoaState` (`✓ std3`).

*Citation.* Michael Streif; Martin Leib (2020). *Forbidden subspaces for level-1 quantum approximate optimization algorithm and instantaneous quantum polynomial circuits*. DOI: [10.1103/PhysRevA.102.042416](https://doi.org/10.1103/PhysRevA.102.042416). URL: <https://arxiv.org/abs/2007.13563v1>.

*Commentary.*

The real function e assigns an energy to every computational basis state. Its values are included in the complex scalars to form the diagonal Hamiltonian. Starting from the uniform state plusState n, apply the diagonal Hamiltonian propagator for time γ, then the mixer propagator for time β. Each propagator is the matrix exponential exp(−itH). This is the one-layer case of the ansatz in main.tex, lines 104–110; the diagonal energies are specified at line 124.

**Definition 1.3 (Exact nonvanishing support).**

$$\forall (n: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})) \to (\mathbb{C})), (\forall (t: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})\right)), ((\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.IsGenuineSuperposition}\left(\psi, t\right)) \Leftrightarrow (\forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), ((\psi\left(x\right) \ne (0: \mathbb{C})) \Leftrightarrow (x \in t))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.IsGenuineSuperposition` (`✓ std3`).

*Citation.* Michael Streif; Martin Leib (2020). *Forbidden subspaces for level-1 quantum approximate optimization algorithm and instantaneous quantum polynomial circuits*. DOI: [10.1103/PhysRevA.102.042416](https://doi.org/10.1103/PhysRevA.102.042416). URL: <https://arxiv.org/abs/2007.13563v1>.

*Commentary.*

A vector ψ is a genuine superposition of t when its amplitude is nonzero at exactly the basis states belonging to t. Thus every amplitude on t is nonzero and every amplitude outside t vanishes. The predicate imposes no normalization condition on an arbitrary vector. The source's notion of a genuine superposition appears in main.tex, line 336.

**Definition 1.4 (The exclusion of intermediate target dimensions).**

$$(\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (e: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})) \to (\mathbb{R})), (\forall (\beta: \mathbb{R}), (\forall (\gamma: \mathbb{R}), (\forall (t: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})\right)), (((2: \mathbb{N}) < \operatorname{Finset.card}\left(t\right)) \to ((\operatorname{Finset.card}\left(t\right) < (2: \mathbb{N})^{n}) \to (\neg (\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.IsGenuineSuperposition}\left(\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.qaoaState}\left(n, e, \beta, \gamma\right), t\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michael Streif; Martin Leib (2020). *Forbidden subspaces for level-1 quantum approximate optimization algorithm and instantaneous quantum polynomial circuits*. DOI: [10.1103/PhysRevA.102.042416](https://doi.org/10.1103/PhysRevA.102.042416). URL: <https://arxiv.org/abs/2007.13563v1>.

*Commentary.*

The exclusion asserts that every real diagonal energy function, at every pair of real angles, fails to produce a genuine superposition of any target set whose cardinality is strictly between two and two to the power n. This is the unrestricted reading of the exclusion stated in the abstract, main.tex line 71. The argument at line 336 assumes that only odd multiples of π/4 can solve the necessary condition; line 341 states that angle restriction as a conjecture. The displayed assertion contains no such restriction and imposes no condition relating t to the ground states of e.

**Theorem 1.5 (Four nonzero amplitudes at mixing angle π/8).**

$$\neg (\operatorname{D5.S3.Quantum.Dynamics.LevelOneQAOAGenuineSuperposition.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.result` (`✓ std3`). ∎

*Resolves.* `Problems/streif-leib-2020-level-one-qaoa-genuine-superposition` (refuted) by `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"streif-leib-2020-level-one-qaoa-genuine-superposition","declaration_gid":"D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michael Streif; Martin Leib (2020). *Forbidden subspaces for level-1 quantum approximate optimization algorithm and instantaneous quantum polynomial circuits*. DOI: [10.1103/PhysRevA.102.042416](https://doi.org/10.1103/PhysRevA.102.042416). URL: <https://arxiv.org/abs/2007.13563v1>.

*Commentary.*

Take three qubits. Let T consist of the bit strings x with x 0 ≠ x 1, and let the energy be 2π when x 0 = x 1 and π/2 otherwise. Choose γ = 1 and β = π/8. Let u be the vector with every coordinate equal to one, and let p have coordinate one when the first two bits agree and minus one when they differ.

Multiplication by the mixer sums a vector's values over the three single-bit flips. It therefore sends u to 3u. Flipping either of the first two bits negates p, while flipping the third preserves p, so it sends p to −p. The exponential action on an eigenvector then gives the mixing phases exp(−3βi) on u and exp(βi) on p.

The uniform initial amplitude is a, the inverse of the complex inclusion of √8. This agrees with the three-qubit amplitude (√2)⁻³ because √8 = (√2)³. The diagonal exponential acts coordinate by coordinate. At time one its phases are exp(−2πi) = 1 where the first two bits agree and exp(−πi/2) = −i where they differ. Consequently the phase layer produces a(1−i)u/2 + a(1+i)p/2.

At β = π/8 the identity −3βi = −πi/2 + βi gives exp(−3βi) = −i exp(βi). Apply the two mixing phases to the preceding decomposition. Where p equals one the two contributions cancel. Where p equals minus one they sum to −a(1+i)exp((π/8)i). Thus the output amplitude is zero exactly when the first two bits agree, and is the same nonzero coefficient at every other coordinate.

The coefficient is nonzero: √8 is strictly positive, its complex inverse and its negative are nonzero, 1+i has positive real part, and a complex exponential never vanishes. Enumerating the three-bit strings gives T = {010, 011, 100, 101} and cardinality four. The amplitude formula therefore proves that the output is a genuine superposition of T. Since 2 < 4 < 2³, applying the exclusion to these energies, angles and target set contradicts that genuine superposition.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.IsGenuineSuperposition`
- Truth anchor: `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.mixer`
- Truth anchor: `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.qaoaState`
- Truth anchor: `D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition.result`
- Dependency: [D5/S3/Combinatorics/IsingUniquenessSets](../../Combinatorics/IsingUniquenessSets.md)
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation](../Entanglement/RandomizedGraphNegativityRefutation.md)
