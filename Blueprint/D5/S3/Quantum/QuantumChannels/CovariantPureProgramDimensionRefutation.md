# Pure covariant programs do not match the mixed dimension

## Abstract

An irreducible representation of the dihedral group of order eight admits a mixed qubit program, while pure qubit programs fail.

**Definition 1.1 (Covariance).**

$$\forall (G : Type), ([\operatorname{Group}\left(G\right)] \forall (d1 : \mathbb{N}), (\forall (d2 : \mathbb{N}), (\forall (U : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d1\right), \mathbb{C}\right)\right)), (\forall (V : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d2\right), \mathbb{C}\right)\right)), (\forall (T : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d2\right), \operatorname{Fin}\left(d2\right), \mathbb{C}\right)), (\operatorname{IsCovariant}\left(U, V, T\right) \Leftrightarrow \forall (g : G), (\forall (rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right)), (T\left((U\left(g\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right)) \cdot rho \cdot \operatorname{star}\left((U\left(g\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right))\right)\right) = (V\left(g\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(d2\right), \operatorname{Fin}\left(d2\right), \mathbb{C}\right)) \cdot T\left(rho\right) \cdot \operatorname{star}\left((V\left(g\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(d2\right), \operatorname{Fin}\left(d2\right), \mathbb{C}\right))\right)))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.IsCovariant` (`✓ std3`).

*Citation.* Martina Gschwendtner, Andreas Bluhm, Andreas Winter (2021). *Programmability of covariant quantum channels*. DOI: [10.22331/q-2021-06-29-488](https://doi.org/10.22331/q-2021-06-29-488). URL: <https://arxiv.org/abs/2012.00717v2>.

*Commentary.*

PDF p. 4, Definition 10: “We call T UV-covariant if” T(Ug A Ug* ) = Vg T(A) Vg* for every A and g. Here U and V are unitary-valued MonoidHom maps. Every represented group element is explicitly coerced to Matrix before multiplication and star.

**Definition 1.2 (Exact mixed programmability).**

$$\forall (G : Type), ([\operatorname{Group}\left(G\right)] \forall (d1 : \mathbb{N}), (\forall (d2 : \mathbb{N}), (\forall (U : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d1\right), \mathbb{C}\right)\right)), (\forall (V : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d2\right), \mathbb{C}\right)\right)), (\forall (dP : \mathbb{N}), (\operatorname{MixedProgrammable}\left(U, V, dP\right) \Leftrightarrow \exists (P : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(dP\right), \operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(dP\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d2\right), \operatorname{Fin}\left(d2\right), \mathbb{C}\right)), (\operatorname{IsChannel}\left(P\right) \land \forall (T : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d2\right), \operatorname{Fin}\left(d2\right), \mathbb{C}\right)), (\left(\operatorname{IsChannel}\left(T\right) \land \operatorname{IsCovariant}\left(U, V, T\right)\right) \Rightarrow \exists (pi : \operatorname{Matrix}\left(\operatorname{Fin}\left(dP\right), \operatorname{Fin}\left(dP\right), \mathbb{C}\right)), (\operatorname{IsDensity}\left(pi\right) \land \forall (rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right)), (P\left(\operatorname{kronecker}\left(rho, pi\right)\right) = T\left(rho\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.MixedProgrammable` (`✓ std3`).

*Citation.* Martina Gschwendtner, Andreas Bluhm, Andreas Winter (2021). *Programmability of covariant quantum channels*. DOI: [10.22331/q-2021-06-29-488](https://doi.org/10.22331/q-2021-06-29-488). URL: <https://arxiv.org/abs/2012.00717v2>.

*Commentary.*

PDF p. 5, Definition 12: “Let H₁ and H₂ be separable Hilbert spaces. Then we call P ∈ CPTP(H₁ ⊗ Hₚ,H₂), with finite-dimensional Hₚ, an ε-programmable quantum processor for a set C ⊂ CPTP(H₁,H₂) of channels (ε-PQP_C), if for every quantum channel T ∈ C there exists a state π_T ∈ D(Hₚ) such that” one half of the diamond distance is at most ε. At ε = 0 this is equality on every input matrix. The set C here is all UV-covariant channels, and dP is the program dimension. IsDensity is the SLDSpectralEnergy predicate: positive semidefinite with trace one on Matrix. kronecker is Matrix.kronecker.

**Definition 1.3 (Exact pure programmability).**

$$\forall (G : Type), ([\operatorname{Group}\left(G\right)] \forall (d1 : \mathbb{N}), (\forall (d2 : \mathbb{N}), (\forall (U : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d1\right), \mathbb{C}\right)\right)), (\forall (V : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d2\right), \mathbb{C}\right)\right)), (\forall (dP : \mathbb{N}), (\operatorname{PureProgrammable}\left(U, V, dP\right) \Leftrightarrow \exists (P : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(dP\right), \operatorname{Fin}\left(d1\right) \times \operatorname{Fin}\left(dP\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d2\right), \operatorname{Fin}\left(d2\right), \mathbb{C}\right)), (\operatorname{IsChannel}\left(P\right) \land \forall (T : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d2\right), \operatorname{Fin}\left(d2\right), \mathbb{C}\right)), (\left(\operatorname{IsChannel}\left(T\right) \land \operatorname{IsCovariant}\left(U, V, T\right)\right) \Rightarrow \exists (psi : \operatorname{Fin}\left(dP\right) \to \mathbb{C}), (\operatorname{dotProduct}\left(\operatorname{star}\left(psi\right), psi\right) = 1 \land \forall (rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right)), (P\left(\operatorname{kronecker}\left(rho, \operatorname{rankOneDensity}\left(psi\right)\right)\right) = T\left(rho\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.PureProgrammable` (`✓ std3`).

*Citation.* Martina Gschwendtner, Andreas Bluhm, Andreas Winter (2021). *Programmability of covariant quantum channels*. DOI: [10.22331/q-2021-06-29-488](https://doi.org/10.22331/q-2021-06-29-488). URL: <https://arxiv.org/abs/2012.00717v2>.

*Commentary.*

PDF p. 6, Remark 13: “In the literature, where the set of channels C often consists of isometries or even unitaries, it is customary to impose that the program state π_T is pure.” PureProgrammable uses the same processor condition with a normalized vector psi and its rankOneDensity. star psi dotProduct psi = 1 is the unit-norm convention.

**Definition 1.4 (The affirmative answer).**

$$claim \Leftrightarrow \forall (G : Type), ([\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] \forall (d1 : \mathbb{N}), (\forall (d2 : \mathbb{N}), (\forall (U : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d1\right), \mathbb{C}\right)\right)), (\forall (V : \operatorname{MonoidHom}\left(G, \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d2\right), \mathbb{C}\right)\right)), (\operatorname{IrredProj}\left((\lambda g : G, (U\left(g\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(d1\right), \operatorname{Fin}\left(d1\right), \mathbb{C}\right)))\right) \Rightarrow \forall (dP : \mathbb{N}), (\operatorname{MixedProgrammable}\left(U, V, dP\right) \Rightarrow \operatorname{PureProgrammable}\left(U, V, dP\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.claim` (`✓ std3`).

*Citation.* Martina Gschwendtner, Andreas Bluhm, Andreas Winter (2021). *Programmability of covariant quantum channels*. DOI: [10.22331/q-2021-06-29-488](https://doi.org/10.22331/q-2021-06-29-488). URL: <https://arxiv.org/abs/2012.00717v2>.

*Commentary.*

PDF p. 21, Section 5: “We leave it as an open question whether the upper bounds can be improved to match the lower ones also for pure program states.” G ranges over finite groups, which are compact with the discrete topology. The source's irreducibility sentence on PDF p. 3 is: “A unitary representation U of a group G on a finite-dimensional vector space H₁ is called irreducible representation (irrep) if and only if the only invariant subspaces of {Ug | g ∈ G} are {0} and the whole space.” The frozen IrredProj expresses exactly this invariant-subspace condition on EuclideanSpace; WithLp.linearEquiv transports it to the coordinate space Fin d1 → complex. The source's Theorems 25 and 31 make mixed dimension optimal at d_c = sum n_k; matching every mixed dimension therefore expresses the affirmative answer. A finite-group counterexample refutes the full compact-group question.

**Theorem 1.5 (A negative answer).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gschwendtner-bluhm-winter-2021-pure-program-states` (refuted) by `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gschwendtner-bluhm-winter-2021-pure-program-states","declaration_gid":"D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Martina Gschwendtner, Andreas Bluhm, Andreas Winter (2021). *Programmability of covariant quantum channels*. DOI: [10.22331/q-2021-06-29-488](https://doi.org/10.22331/q-2021-06-29-488). URL: <https://arxiv.org/abs/2012.00717v2>.

*Commentary.*

Take G = DihedralGroup 4, d1 = d2 = dP = 2, U generated by [[0,−1],[1,0]] and diag(1,−1), and V the trivial representation. Here the conjugate representation of U tensor V contains two copies of the irreducible conjugate of U, so d_c = 2. Averaging over the eight group elements gives trace(rho) times one half of the identity. Thus every UV-covariant channel is a replacement channel rho ↦ trace(rho) sigma. Tracing out the input implements all of them with mixed programs of dimension two. Pure programs of dimension two would have to produce the two basis targets, their equal superposition target, and one half of the identity. The qubit obstruction excludes these four outputs. This proves the dimension-two refutation. Exact pure optima in larger dimensions and the general multiplicity bounds require separate arguments.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.IsCovariant`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.MixedProgrammable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.PureProgrammable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/CovariantPureProgramDimensionRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer](../Information/NiceErrorBasisNonNormalStabilizer.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PureProgramQubitObstruction](PureProgramQubitObstruction.md)
