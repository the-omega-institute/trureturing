# Temporal Bell contractions in the open XX chain

## Abstract

The endpoint vacuum contractions of the open XX chain equal a difference of one-particle propagator entries.

Sites are indexed from zero. Assignment N is the type Fin N → Bool of occupation configurations, and FullOperator N is the complex matrix algebra on these configurations. The operator fullC j is the Jordan–Wigner annihilator at j; Matrix.conjTranspose is the adjoint. Scalar multiplication is denoted by a centered dot, and adjacent matrix factors are multiplied in their displayed order. Complex.ofReal explicitly includes a real scalar in the complex numbers, and Fin.val takes a bounded index to its natural value. Natural subtraction is truncated at zero. Fin.mk displays its natural value with the bound proof suppressed; the positivity proof in sigmaXLast is also suppressed when it is determined by the hypothesis N ≥ 2. All other binders, including the positivity argument in the definition of sigmaXLast, are displayed.

**Definition 1.1 (The open-chain one-particle Hamiltonian).**

$$\forall (N: \mathbb{N}), (\forall (J: \mathbb{R}), (\forall (\mu: \mathbb{R}), ((\operatorname{hopping}\left(N, J, \mu\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)) = \lambda (i: \operatorname{Fin}\left(N\right)) \mapsto (\lambda (j: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{ite}\left((i = j), (-(\operatorname{Complex.ofReal}\left(\mu\right))), (\operatorname{ite}\left((((\operatorname{Fin.val}\left(i\right)) + ((1: \mathbb{N})) = \operatorname{Fin.val}\left(j\right)) \lor ((\operatorname{Fin.val}\left(j\right)) + ((1: \mathbb{N})) = \operatorname{Fin.val}\left(i\right))), (-(\operatorname{Complex.ofReal}\left(J\right))), ((0: \mathbb{C}))\right))\right))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.hopping` (`✓ std3`).

*Citation.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

The diagonal entries are minus the chemical potential μ. Nearest-neighbor entries are minus the hopping strength J, and all other entries vanish. This is the one-particle matrix of the fermionic Hamiltonian in the source, arxiv.tex lines 144–150; only sites with adjacent natural indices are coupled.

**Definition 1.2 (The quadratic many-particle Hamiltonian).**

$$\forall (N: \mathbb{N}), (\forall (J: \mathbb{R}), (\forall (\mu: \mathbb{R}), ((\operatorname{hamiltonian}\left(N, J, \mu\right): \operatorname{FullOperator}\left(N\right)) = \sum_{(i: \operatorname{Fin}\left(N\right))} (\sum_{(j: \operatorname{Fin}\left(N\right))} ((\operatorname{hopping}\left(N, J, \mu, i, j\right)) \cdot ((\operatorname{Matrix.conjTranspose}\left(\operatorname{fullC}\left(i\right)\right)) \cdot (\operatorname{fullC}\left(j\right))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.hamiltonian` (`✓ std3`).

*Citation.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

Sum the creation-annihilation products with coefficients from hopping. This is the source's Jordan–Wigner form of the open XX Hamiltonian, arxiv.tex lines 144–150, on the full occupation space. The sums and the definition include the empty chain.

**Definition 1.3 (The propagator defined by the matrix exponential).**

$$\forall (N: \mathbb{N}), (\forall (J: \mathbb{R}), (\forall (\mu: \mathbb{R}), (\forall (t: \mathbb{R}), ((\operatorname{propagator}\left(N, J, \mu, t\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{C}\right)) = \operatorname{NormedSpace.exp}\left(((\operatorname{Complex.ofReal}\left(t\right)) \cdot (\operatorname{Complex.I})) \cdot (\operatorname{hopping}\left(N, J, \mu\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.propagator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

The complex matrix exponential of it times the one-particle Hamiltonian gives the coefficients of evolved creation operators. Thus G is read through the source's relation f†ⱼ(t) = ∑ᵢ Gᵢⱼ(t)f†ᵢ in arxiv.tex lines 153–154 and 291. The definition fixes the hopping sign through hopping and does not use the printed spectral expression for the eigenfunctions.

**Definition 1.4 (Heisenberg evolution).**

$$\forall (N: \mathbb{N}), (\forall (J: \mathbb{R}), (\forall (\mu: \mathbb{R}), (\forall (t: \mathbb{R}), (\forall (A: \operatorname{FullOperator}\left(N\right)), ((\operatorname{evolve}\left(J, \mu, t, A\right): \operatorname{FullOperator}\left(N\right)) = ((\operatorname{NormedSpace.exp}\left(((\operatorname{Complex.ofReal}\left(t\right)) \cdot (\operatorname{Complex.I})) \cdot (\operatorname{hamiltonian}\left(N, J, \mu\right))\right)) \cdot (A)) \cdot (\operatorname{NormedSpace.exp}\left(-(((\operatorname{Complex.ofReal}\left(t\right)) \cdot (\operatorname{Complex.I})) \cdot (\operatorname{hamiltonian}\left(N, J, \mu\right)))\right)))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.evolve` (`✓ std3`).

*Citation.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

Conjugate A by the exponential of itH, with the inverse exponential on the right. This is the Heisenberg convention used for the creation operators in arxiv.tex line 291. All three parameters J, μ and t are real; no sign restriction is imposed.

**Definition 1.5 (The last-site spin observable).**

$$\forall (N: \mathbb{N}), (\forall (hN: (0: \mathbb{N}) < N), ((\operatorname{sigmaXLast}\left(N, hN\right): \operatorname{FullOperator}\left(N\right)) = (\operatorname{List.prod}\left(\operatorname{List.map}\left(\lambda (j: \operatorname{Fin}\left(N\right)) \mapsto (((1: \operatorname{FullOperator}\left(N\right))) - (((2: \mathbb{C})) \cdot ((\operatorname{Matrix.conjTranspose}\left(\operatorname{fullC}\left(j\right)\right)) \cdot (\operatorname{fullC}\left(j\right))))), \operatorname{List.filter}\left(\lambda (j: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{Decidable.decide}\left(\operatorname{Fin.val}\left(j\right) < (N) - ((1: \mathbb{N}))\right)), \operatorname{List.finRange}\left(N\right)\right)\right)\right)) \cdot ((\operatorname{Matrix.conjTranspose}\left(\operatorname{fullC}\left((\operatorname{Fin.mk}\left((N) - ((1: \mathbb{N}))\right): \operatorname{Fin}\left(N\right))\right)\right)) + (\operatorname{fullC}\left((\operatorname{Fin.mk}\left((N) - ((1: \mathbb{N}))\right): \operatorname{Fin}\left(N\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.sigmaXLast` (`✓ std3`).

*Citation.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

For a positive chain length, multiply the factors 1 − 2f†ⱼfⱼ over the sites strictly before N − 1, in increasing order, and then multiply by f† at the last site plus f at that site. List.finRange supplies the increasing list of sites, List.filter retains the prefix, List.map forms the factors, and List.prod multiplies them. The Boolean filter explicitly decides the natural inequality. This is σˣ at the last site under the inverse Jordan–Wigner transformation, arxiv.tex lines 285–286 and 291.

**Definition 1.6 (The empty occupation configuration).**

$$\forall (N: \mathbb{N}), (\forall (x: \operatorname{Fin}\left(N\right)), ((\operatorname{vacuumIndex}\left(N\right): \operatorname{Assignment}\left(N\right))\left(x\right) = \operatorname{Bool.false}))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.vacuumIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

The pointwise defining equality states that the vacuum has false occupation at every site. Its row and column select the vacuum matrix element of any full operator. The argument x ranges over Fin N, including the empty type when N is zero.

**Definition 1.7 (The endpoint contraction identity).**

$$(\operatorname{claim}: \operatorname{Prop}) = (\forall (N: \mathbb{N}), (((2: \mathbb{N}) \le N) \Rightarrow (\forall (J: \mathbb{R}), (\forall (\mu: \mathbb{R}), (\forall (t: \mathbb{R}), (\operatorname{let} (first: \operatorname{Fin}\left(N\right)) := ((\operatorname{Fin.mk}\left((0: \mathbb{N})\right): \operatorname{Fin}\left(N\right))); (\operatorname{let} (last: \operatorname{Fin}\left(N\right)) := ((\operatorname{Fin.mk}\left((N) - ((1: \mathbb{N}))\right): \operatorname{Fin}\left(N\right))); (\operatorname{let} (X: \operatorname{FullOperator}\left(N\right)) := (\operatorname{evolve}\left(J, \mu, t, \operatorname{sigmaXLast}\left(N\right)\right)); (\operatorname{Complex.re}\left(((((((\operatorname{fullC}\left(last\right)) \cdot (\operatorname{fullC}\left(first\right))) \cdot (X)) \cdot (\operatorname{Matrix.conjTranspose}\left(\operatorname{fullC}\left(first\right)\right)))\left(\operatorname{vacuumIndex}\left(N\right), \operatorname{vacuumIndex}\left(N\right)\right)) + (((((\operatorname{fullC}\left(last\right)) \cdot (\operatorname{fullC}\left(first\right))) \cdot (X)) \cdot (\operatorname{Matrix.conjTranspose}\left(\operatorname{fullC}\left(last\right)\right)))\left(\operatorname{vacuumIndex}\left(N\right), \operatorname{vacuumIndex}\left(N\right)\right)))\right) = \operatorname{Complex.re}\left(((\operatorname{propagator}\left(N, J, \mu, t, last, last\right)) - (\operatorname{propagator}\left(N, J, \mu, t, first, last\right)))\right))))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

For every N at least two and every real J, μ and t, evolve the last-site spin observable and evaluate the two displayed vacuum contractions. Their sum has the same real part as the last diagonal propagator entry minus its first-row, last-column entry. This reads the conjecture in arxiv.tex lines 343–353 with G defined by the creation-operator evolution relation. The hypothesis N ≥ 2 makes first and last distinct and supplies the positive chain length needed by sigmaXLast.

**Theorem 1.8 (The identity for every chain length at least two).**

$$\forall (N: \mathbb{N}), (((2: \mathbb{N}) \le N) \Rightarrow (\forall (J: \mathbb{R}), (\forall (\mu: \mathbb{R}), (\forall (t: \mathbb{R}), (\operatorname{let} (first: \operatorname{Fin}\left(N\right)) := ((\operatorname{Fin.mk}\left((0: \mathbb{N})\right): \operatorname{Fin}\left(N\right))); (\operatorname{let} (last: \operatorname{Fin}\left(N\right)) := ((\operatorname{Fin.mk}\left((N) - ((1: \mathbb{N}))\right): \operatorname{Fin}\left(N\right))); (\operatorname{let} (X: \operatorname{FullOperator}\left(N\right)) := (\operatorname{evolve}\left(J, \mu, t, \operatorname{sigmaXLast}\left(N\right)\right)); (\operatorname{Complex.re}\left(((((((\operatorname{fullC}\left(last\right)) \cdot (\operatorname{fullC}\left(first\right))) \cdot (X)) \cdot (\operatorname{Matrix.conjTranspose}\left(\operatorname{fullC}\left(first\right)\right)))\left(\operatorname{vacuumIndex}\left(N\right), \operatorname{vacuumIndex}\left(N\right)\right)) + (((((\operatorname{fullC}\left(last\right)) \cdot (\operatorname{fullC}\left(first\right))) \cdot (X)) \cdot (\operatorname{Matrix.conjTranspose}\left(\operatorname{fullC}\left(last\right)\right)))\left(\operatorname{vacuumIndex}\left(N\right), \operatorname{vacuumIndex}\left(N\right)\right)))\right) = \operatorname{Complex.re}\left(((\operatorname{propagator}\left(N, J, \mu, t, last, last\right)) - (\operatorname{propagator}\left(N, J, \mu, t, first, last\right)))\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/tononi-lewenstein-2025-temporal-bell-contraction-identity` (proved) by `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tononi-lewenstein-2025-temporal-bell-contraction-identity","declaration_gid":"D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrea Tononi; Maciej Lewenstein (2025). *Temporal Bell inequalities in non-relativistic many-body physics*. DOI: [10.1088/2058-9565/adcbce](https://doi.org/10.1088/2058-9565/adcbce). URL: <https://arxiv.org/abs/2409.17290v4>.

*Commentary.*

Write fⱼ = fullC j, h = hopping N J μ and H = hamiltonian N J μ. Taking adjoints of the distinct-site annihilation anticommutators gives the corresponding creation anticommutators. At a single site, write the two Majorana operators as fⱼ + f†ⱼ and i(fⱼ − f†ⱼ); their Clifford relations give four times the creation self-anticommutator equal to zero, hence that anticommutator vanishes. Together with the mixed canonical anticommutation relation, these identities imply [f†ᵢfₖ, f†ⱼ] = δₖⱼf†ᵢ. Summing with the hopping coefficients gives [H,f†ⱼ] = ∑ᵢ hᵢⱼf†ᵢ.

For a fixed j, let L(M) = ∑ᵢ Mᵢⱼf†ᵢ, a complex linear map from one-particle matrices to full operators. The commutator identity gives H L(M) − L(M) H = L(hM). For complex z, differentiate F(z) = exp(−zH)L(exp(zh))exp(zH). The product rule and the commutator identity cancel all three derivative terms, so F has derivative zero everywhere and is constant. At zero, L(1) = f†ⱼ. Multiplying by the inverse exponentials and setting z = Complex.ofReal(t)i therefore gives evolve J μ t f†ⱼ = ∑ᵢ Gᵢⱼ(t)f†ᵢ. The hopping matrix has conjugate-symmetric entries; taking the adjoint of the finite double sum and interchanging its indices proves H Hermitian. Consequently evolution preserves adjoints, and taking the adjoint of the creation formula gives evolve J μ t fⱼ = ∑ᵢ conjugate(Gᵢⱼ(t))fᵢ.

Let P be number parity. Its anticommutation with the two Majorana operators, separated into their sum and difference, shows that P anticommutes with each fⱼ and f†ⱼ. In the occupation basis, f†ⱼfⱼ is diagonal with entry one exactly when site j is occupied. Thus 1 − 2f†ⱼfⱼ is diagonal with entry minus one at an occupied site and plus one at an empty site. Multiplying these diagonal matrices over the prefix and then the last site gives P, whose entry is minus one to the total occupation count. The creation self-anticommutator and CAR_nilpotent give (f†ⱼ)² = 0; taking adjoints gives fⱼ² = 0. The single-site mixed relation then yields (1 − 2f†ⱼfⱼ)(fⱼ − f†ⱼ) = f†ⱼ + fⱼ. Combining the prefix product with this equality expresses the last-site spin observable as P(f_last − f†_last).

Moving P through one creation operator and one annihilation operator changes the sign twice, so P commutes with every f†ᵢfⱼ and hence with H. Its Heisenberg evolution is therefore P. Conjugation by an invertible exponential preserves products and differences. Applying these facts and the two evolution formulas gives the evolved last-site spin observable as P(∑ᵢ conjugate(Gᵢ,last(t))fᵢ − ∑ᵢ Gᵢ,last(t)f†ᵢ).

Every annihilator kills the empty occupation column, and every creator kills its adjoint row. The mixed anticommutation relation then gives ⟨0|fᵢf†ⱼ|0⟩ = δᵢⱼ. For arbitrary sites a, b, k and r, commute the two creators to the left to obtain ⟨0|f_b f_a f†_k f†_r|0⟩ = δₐₖδᵦᵣ − δᵦₖδₐᵣ. Commuting the last creator past an annihilator also gives ⟨0|f_b f_a f_k f†_r|0⟩ = 0. For a ≠ b and arbitrary coefficient functions u and v, move P to the left through f_b f_a. The two sign changes cancel and the vacuum row of P has value one, so parity disappears from the contractions. Expanding the sums, the annihilation terms vanish and the four-operator formula shows that the contraction with f†_a equals v b, while the contraction with f†_b equals −v a. Their sum is v b − v a.

Take a = first, b = last, u i = conjugate(Gᵢ,last(t)) and v i = Gᵢ,last(t). Since N ≥ 2, first and last are distinct. Substitution of the evolved observable therefore proves the complex identity: the two vacuum contractions sum to G_last,last(t) − G_first,last(t). Taking Complex.re of both sides gives the stated real-part identity.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.evolve`
- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.hamiltonian`
- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.hopping`
- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.propagator`
- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.sigmaXLast`
- Truth anchor: `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.vacuumIndex`
- Dependency: [D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation](../Fermionic/PeriodicSshExcessPseudoEntropyRefutation.md)
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum](../Measurements/CliffordJointMeasurability/FourierCliffordVacuum.md)
