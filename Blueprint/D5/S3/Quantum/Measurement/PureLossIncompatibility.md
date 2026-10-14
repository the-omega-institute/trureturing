# Binary measurement incompatibility under pure loss

## Abstract

For every natural n at least one, some n+1 binary measurements on the full one-mode Fock space remain incompatible under pure loss of transmissivity 1/n.

The one-mode Hilbert space consists of square-summable complex sequences. The outer coordinate of the two-mode space indexes the environment; each coordinate is a vector of the retained mode. ContinuousLinearMap denotes continuous complex-linear maps, and the operator 1 is the identity. All occupation numbers are included. Named objects retain their Lean namespaces, and a natural number annotated as real denotes its real cast.

**Definition 1.1 (The one-mode Fock space).**

$$\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H} = \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.FockSpace}$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponent two gives the Hilbert norm on the completed one-mode Fock space.

**Definition 1.2 (The retained mode and its environment).**

$$\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.K} = \operatorname{lp}\left(\lambda (\mathord{\cdot}: \mathbb{N}) \mapsto (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}), 2\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vector is a square-summable family of retained-mode vectors indexed by the environment occupation number.

**Definition 1.3 (Bounded operators on the retained mode).**

$$\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op} = \operatorname{ContinuousLinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{C}\right), \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}, \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.Op` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are continuous complex-linear endomorphisms of the one-mode Hilbert space.

**Definition 1.4 (An operator acting in every environment coordinate).**

$$\forall (M: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}), (\forall (w: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.K}), (\forall (k: \mathbb{N}), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.amplify}\left(M\right)\left(w\right)\left(k\right) = M\left(w\left(k\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.amplify` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Amplification uses lp.mapCLM to apply the same retained-mode operator to each environment coordinate. The equation characterizes its action on every vector.

**Definition 1.5 (Embedding with a vacuum environment).**

$$\forall (v: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.vacuumEmbedding}\left(v\right) = \operatorname{lp.single}\left(2, 0, v\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.vacuumEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The retained vector occupies environment coordinate zero. All other environment coordinates vanish; lp.single has exponent two and values in the retained-mode Hilbert space.

**Definition 1.6 (The beam-splitter dilation).**

$$\forall (tau: \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.stinespring}\left(tau\right) = \operatorname{ContinuousLinearMap.comp}\left(\operatorname{LinearIsometry.toContinuousLinearMap}\left(\operatorname{LinearIsometryEquiv.toLinearIsometry}\left(\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.beamSplitter}\left(\operatorname{Subtype.val}\left(tau\right), \operatorname{Subtype.property}\left(tau\right)\right)\right)\right), \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.vacuumEmbedding}\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.stinespring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

First place the environment in the vacuum, then apply the full two-mode beam splitter. Subtype.val supplies the transmissivity and Subtype.property supplies its interval condition. The isometry is viewed as a continuous linear map.

**Theorem 1.7 (The vacuum embedding is a tensor product).**

$$\forall (v: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.vacuumEmbedding}\left(v\right) = \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.tensor}\left(v, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PureLossIncompatibility.vacuum_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding a retained-mode vector in environment coordinate zero is exactly its tensor product with the environment vacuum.

**Theorem 1.8 (Vacuum through the beam splitter).**

$$\forall (tau: \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.stinespring}\left(tau, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(0\right)\right) = \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.fockPair}\left(0, 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vacuum in both modes is fixed by the beam splitter for every transmissivity in the closed unit interval.

**Theorem 1.9 (One photon through the beam splitter).**

$$\forall (tau: \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.stinespring}\left(tau, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(1\right)\right) = (\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\operatorname{Subtype.val}\left(tau\right)\right)\right)) \cdot (\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.fockPair}\left(1, 0\right)) + (\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(1 - \operatorname{Subtype.val}\left(tau\right)\right)\right)) \cdot (\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.fockPair}\left(0, 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single input photon has retained-mode amplitude sqrt(tau) and environment amplitude sqrt(1-tau), both viewed as complex scalars.

**Theorem 1.10 (Environment slices of the vacuum output).**

$$\forall (tau: \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\forall (k: \mathbb{N}), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.stinespring}\left(tau, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(0\right)\right)\left(k\right) = \operatorname{ite}\left(k = 0, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(0\right), 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_zero_coord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vacuum output has the retained vacuum in environment slice zero and the zero vector in every other slice.

**Theorem 1.11 (Environment slices of the one-photon output).**

$$\forall (tau: \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\forall (k: \mathbb{N}), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.stinespring}\left(tau, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(1\right)\right)\left(k\right) = \operatorname{ite}\left(k = 0, (\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\operatorname{Subtype.val}\left(tau\right)\right)\right)) \cdot (\operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(1\right)), \operatorname{ite}\left(k = 1, (\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(1 - \operatorname{Subtype.val}\left(tau\right)\right)\right)) \cdot (\operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(0\right)), 0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_one_coord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Environment slice zero contains sqrt(tau) times the retained one-photon vector; slice one contains sqrt(1-tau) times the retained vacuum. Every higher environment slice vanishes.

**Definition 1.12 (The dual pure-loss action on effects).**

$$\forall (tau: \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\forall (M: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.dualLoss}\left(tau, M\right) = \operatorname{ContinuousLinearMap.comp}\left(\operatorname{ContinuousLinearMap.adjoint}\left(\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.stinespring}\left(tau\right)\right), \operatorname{ContinuousLinearMap.comp}\left(\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.amplify}\left(M\right), \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.stinespring}\left(tau\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.dualLoss` (`✓ std3`).

*Citation.* Mohammad Mehboudi, Fatemeh Rezaeinia, Saleh Rahimi-Keshari (2025). *Measurement incompatibility under loss*. DOI: [10.1103/s9sp-2fd7](https://doi.org/10.1103/s9sp-2fd7). URL: <https://arxiv.org/abs/2411.05920v3>.

*Commentary.*

Pull the amplified operator back along the vacuum beam-splitter dilation. This operator satisfies the trace relation defining the loss dual and is its unique solution. ContinuousLinearMap.adjoint is the Hilbert-space adjoint, and ContinuousLinearMap.comp is composition.

**Definition 1.13 (The defining trace relation of the loss dual).**

$$\forall (tau: \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\forall (M: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}), (\forall (N: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}), ((\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.IsLossDual}\left(tau, M, N\right)) \Leftrightarrow (\forall (psi: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}), (\operatorname{HasSum}\left(\lambda (n: \mathbb{N}) \mapsto (\operatorname{inner}\left(\mathbb{C}, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(n\right), \operatorname{ContinuousLinearMap.comp}\left(M, \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance.purePartialTrace}\left(\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.beamSplitter}\left(\operatorname{Subtype.val}\left(tau\right), \operatorname{Subtype.property}\left(tau\right)\right)\left(\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.tensor}\left(psi, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(0\right)\right)\right)\right)\right)\left(\operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(n\right)\right)\right)), \operatorname{inner}\left(\mathbb{C}, psi, N\left(psi\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.IsLossDual` (`✓ std3`).

*Citation.* Mohammad Mehboudi, Fatemeh Rezaeinia, Saleh Rahimi-Keshari (2025). *Measurement incompatibility under loss*. DOI: [10.1103/s9sp-2fd7](https://doi.org/10.1103/s9sp-2fd7). URL: <https://arxiv.org/abs/2411.05920v3>.

*Commentary.*

For every pure input psi, apply beamSplitter to tensor psi (e 0) and discard the environment with purePartialTrace. The Fock-basis sum is the trace of M times this output state; HasSum requires convergence to the quadratic form of N. The frozen tensor convention places the environment in the outer sequence coordinate. The vectors e n form the retained-mode Fock basis. This is the source's dual relation on pure states, which determines the bounded operator uniquely.

**Definition 1.14 (A binary positive operator-valued measurement).**

$$\forall (M: \operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}), ((\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.IsBinaryPOVM}\left(M\right)) \Leftrightarrow ((\forall (b: \operatorname{Fin}\left(2\right)), (\operatorname{ContinuousLinearMap.IsPositive}\left(M\left(b\right)\right))) \land (M\left(0\right) + M\left(1\right) = (1: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}))))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.IsBinaryPOVM` (`✓ std3`).

*Citation.* Mohammad Mehboudi, Fatemeh Rezaeinia, Saleh Rahimi-Keshari (2025). *Measurement incompatibility under loss*. DOI: [10.1103/s9sp-2fd7](https://doi.org/10.1103/s9sp-2fd7). URL: <https://arxiv.org/abs/2411.05920v3>.

*Commentary.*

Both effects are positive and their sum is the identity. The outcomes are labelled zero and one. Positivity is ContinuousLinearMap.IsPositive.

**Definition 1.15 (A parent with all binary-string marginals).**

$$\forall (m: \mathbb{N}), (\forall (F: \operatorname{Fin}\left(m\right) \to \left(\operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}\right)), ((\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.HasParent}\left(F\right)) \Leftrightarrow (\exists (G: (\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}), ((\forall (a: (\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{ContinuousLinearMap.IsPositive}\left(G\left(a\right)\right))) \land ((\sum_{(a: (\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right)))} (G\left(a\right)) = (1: \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op})) \land (\forall (j: \operatorname{Fin}\left(m\right)), (\forall (b: \operatorname{Fin}\left(2\right)), (\sum_{a \in \operatorname{Finset.filter}\left(\lambda (a: (\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right))) \mapsto (a\left(j\right) = b), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(2\right))\right))\right)} (G\left(a\right)) = F\left(j, b\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.HasParent` (`✓ std3`).

*Citation.* Mohammad Mehboudi, Fatemeh Rezaeinia, Saleh Rahimi-Keshari (2025). *Measurement incompatibility under loss*. DOI: [10.1103/s9sp-2fd7](https://doi.org/10.1103/s9sp-2fd7). URL: <https://arxiv.org/abs/2411.05920v3>.

*Commentary.*

The parent assigns a positive effect to every function from Fin m to Fin 2, and the effects sum to the identity. For each setting j and outcome b, sum over all strings whose j-th outcome is b. Equality with F(j,b) is the joint-measurability condition of Result 2 and Eq. (3). No outcome string is omitted.

**Definition 1.16 (The admissible reciprocal transmissivity).**

$$\forall (n: \mathbb{N}), (\forall (hn: 1 \le n), (\operatorname{Subtype.val}\left(\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.inverseTransmissivity}\left(n, hn\right)\right) = \frac{1}{(n: \mathbb{R})}))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.inverseTransmissivity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n at least one, the reciprocal real value belongs to the closed unit interval. The parameter hn expresses this lower bound on n.

**Definition 1.17 (Incompatibility at reciprocal integer transmissivity).**

$$(\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (hn: 1 \le n), (\exists (M: \operatorname{Fin}\left(n + 1\right) \to \left(\operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}\right)), ((\forall (j: \operatorname{Fin}\left(n + 1\right)), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.IsBinaryPOVM}\left(M\left(j\right)\right))) \land ((\exists (N: \operatorname{Fin}\left(n + 1\right) \to \left(\operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}\right)), (\forall (j: \operatorname{Fin}\left(n + 1\right)), (\forall (b: \operatorname{Fin}\left(2\right)), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.IsLossDual}\left(\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.inverseTransmissivity}\left(n, hn\right), M\left(j, b\right), N\left(j, b\right)\right))))) \land (\forall (N: \operatorname{Fin}\left(n + 1\right) \to \left(\operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.Op}\right)), ((\forall (j: \operatorname{Fin}\left(n + 1\right)), (\forall (b: \operatorname{Fin}\left(2\right)), (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.IsLossDual}\left(\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.inverseTransmissivity}\left(n, hn\right), M\left(j, b\right), N\left(j, b\right)\right)))) \Rightarrow \left(\neg (\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.HasParent}\left(N\right))\right))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/PureLossIncompatibility.claim` (`✓ std3`).

*Citation.* Mohammad Mehboudi, Fatemeh Rezaeinia, Saleh Rahimi-Keshari (2025). *Measurement incompatibility under loss*. DOI: [10.1103/s9sp-2fd7](https://doi.org/10.1103/s9sp-2fd7). URL: <https://arxiv.org/abs/2411.05920v3>.

*Commentary.*

Result 3 asserts the existence of n+1 measurements that remain incompatible at transmissivity 1/n. Their dual images exist by the defining trace relation. Every family satisfying that relation has no parent with the displayed marginals. Every natural n at least one is included, also n=1.

**Theorem 1.18 (Incompatible binary measurements for every n).**

$$\operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PureLossIncompatibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/mehboudi-rezaeinia-rahimi-keshari-2025-loss-incompatibility` (proved) by `D5/S3/Quantum/Measurement/PureLossIncompatibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mehboudi-rezaeinia-rahimi-keshari-2025-loss-incompatibility","declaration_gid":"D5/S3/Quantum/Measurement/PureLossIncompatibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohammad Mehboudi, Fatemeh Rezaeinia, Saleh Rahimi-Keshari (2025). *Measurement incompatibility under loss*. DOI: [10.1103/s9sp-2fd7](https://doi.org/10.1103/s9sp-2fd7). URL: <https://arxiv.org/abs/2411.05920v3>.

*Commentary.*

The reduced pure output is the sum of the rank-one operators of its environment slices. Their squared norms are summable. Cauchy-Schwarz and the operator norm bound make the double Fock-basis and environment sum absolutely summable. Interchanging the sums and applying Parseval identifies its trace with the quadratic form of dualLoss. Uniqueness of the sum and complex polarization identify every operator satisfying IsLossDual with this pullback.

Use the coherent-state projectors of Eq. (4) and their complements. For m distinct unit phases z_j and a transmissivity tau with m tau > 1, set Delta = m tau - 1, Q = sum over i<j of 1/|z_i-z_j|^2, and x = Delta/(2(m + 4Q)). The coherent amplitudes are sqrt(x) z_j.

Restrict the dual click effects to the span of |0> and |1>. Their matrices have diagonal entries a = 1-exp(-x) and c = 1-exp(-x)(1-tau+tau x), with off-diagonal entries -b conjugate(z_j) and -b z_j, where b = sqrt(tau) exp(-x) sqrt(x). The scalar bounds c-b^2/a <= x and c >= tau-x control these matrices. Any full-space parent would induce a parent of these effects.

The quadratic-form bound for a common subeffect of settings i and j gives its lower diagonal entry at most 4x/|z_i-z_j|^2. For each parent string let k count its click outcomes. The counting identity for pairs of clicks, together with k <= 1 + binomial(k,2), implies m c <= 1 + 4xQ. The chosen x instead gives m c - 1 - 4xQ >= Delta/2 > 0. Finally take m=n+1, tau=1/n and the regular phases z_j = exp(2 pi i j/(n+1)). They are distinct unit complex numbers, and m tau > 1 for every n at least one, proving the proposition.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.H`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.HasParent`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.IsBinaryPOVM`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.IsLossDual`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.K`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.Op`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.amplify`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.dualLoss`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.inverseTransmissivity`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.result`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_one`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_one_coord`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.split_zero_coord`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.stinespring`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.vacuumEmbedding`
- Truth anchor: `D5/S3/Quantum/Measurement/PureLossIncompatibility.vacuum_tensor`
- Dependency: [D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation](../../Estimation/TransmissivityBetaPriorProbeRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator](../QuantumChannels/FockAttenuator/Attenuator.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality](../QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.md)
