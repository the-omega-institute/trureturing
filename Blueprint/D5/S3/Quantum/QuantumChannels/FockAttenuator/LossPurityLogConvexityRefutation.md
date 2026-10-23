# Optical-loss purity need not be log-convex

## Abstract

The purity of a three-level mixed Fock state under vacuum-environment optical loss fails the midpoint inequality for log-convexity.

The one-mode Hilbert space is the full space of square-summable complex sequences. H and Op retain the namespaces of PureLossIncompatibility. The outer coordinate of the two-mode space indexes the environment, which purePartialTrace discards. The vectors e n are the Fock basis. Transmissivity T ranges over the closed unit interval, and hT is its interval-membership proof. Complex.ofReal is the real-to-complex cast; scalar multiplication uses the complex scalar action. Named objects retain their Lean namespaces.

**Definition 1.1 (Loss of a finite ensemble).**

$$\forall (k: \mathbb{N}), (\forall (p: \operatorname{Fin}\left(k\right) \to \mathbb{R}), (\forall (phi: \operatorname{Fin}\left(k\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}), (\forall (T: \mathbb{R}), (\forall (hT: T \in \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation.loss}\left(p, phi, T, hT\right) = \sum_{(i: \operatorname{Fin}\left(k\right))} ((\operatorname{Complex.ofReal}\left(p\left(i\right)\right)) \cdot (\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance.purePartialTrace}\left(\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.beamSplitter}\left(T, hT, \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.tensor}\left(phi\left(i\right), \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(0\right)\right)\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.loss` (`✓ std3`).

*Citation.* Anaelle Hertz, Noah Lupu-Gladstein, Khabat Heshami, Aaron Z. Goldberg (2026). *Equalities and inequalities from entanglement, loss, and beam splitters*. DOI: [10.1007/s40509-026-00402-0](https://doi.org/10.1007/s40509-026-00402-0). URL: <https://arxiv.org/abs/2501.02047v1>.

*Commentary.*

Section I.A, equation (2), defines optical loss by mixing the input with a vacuum environment on a beam splitter and tracing out that environment. The displayed finite sum applies this channel to each pure vector with its real weight. Normalized nonnegative weights and unit vectors are required by claim, rather than by loss itself. T=1 means no loss.

**Definition 1.2 (The convergent Fock-basis trace of the square).**

$$\forall (k: \mathbb{N}), (\forall (p: \operatorname{Fin}\left(k\right) \to \mathbb{R}), (\forall (phi: \operatorname{Fin}\left(k\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}), (\forall (P: \mathbb{R} \to \mathbb{R}), ((\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation.IsPurityCurve}\left(p, phi, P\right)) \Leftrightarrow (\forall (T: \mathbb{R}), (\forall (hT: T \in \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right)), (\operatorname{HasSum}\left(\lambda (n: \mathbb{N}) \mapsto (\operatorname{inner}\left(\mathbb{C}, \operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(n\right), \operatorname{ContinuousLinearMap.comp}\left(\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation.loss}\left(p, phi, T, hT\right), \operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation.loss}\left(p, phi, T, hT\right)\right)\left(\operatorname{D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.e}\left(n\right)\right)\right)), \operatorname{Complex.ofReal}\left(P\left(T\right)\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.IsPurityCurve` (`✓ std3`).

*Citation.* Anaelle Hertz, Noah Lupu-Gladstein, Khabat Heshami, Aaron Z. Goldberg (2026). *Equalities and inequalities from entanglement, loss, and beam splitters*. DOI: [10.1007/s40509-026-00402-0](https://doi.org/10.1007/s40509-026-00402-0). URL: <https://arxiv.org/abs/2501.02047v1>.

*Commentary.*

The purity in Section III and Conjecture 7 is the trace of the square of the output state. HasSum expresses the sum of its Fock-basis diagonal, including convergence and equality to the real value P(T), viewed in Complex. Every T in the closed unit interval is included.

**Definition 1.3 (Conjecture 7 on finite ensembles).**

$$(\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation.claim}) \Leftrightarrow (\forall (k: \mathbb{N}), (\forall (p: \operatorname{Fin}\left(k\right) \to \mathbb{R}), (\forall (phi: \operatorname{Fin}\left(k\right) \to \operatorname{D5.S3.Quantum.Measurement.PureLossIncompatibility.H}), ((\forall (i: \operatorname{Fin}\left(k\right)), (0 \le p\left(i\right))) \Rightarrow ((\sum_{(i: \operatorname{Fin}\left(k\right))} (p\left(i\right)) = 1) \Rightarrow ((\forall (i: \operatorname{Fin}\left(k\right)), (\left\lVert phi\left(i\right) \right\rVert = 1)) \Rightarrow (\exists (P: \mathbb{R} \to \mathbb{R}), ((\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation.IsPurityCurve}\left(p, phi, P\right)) \land (\operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Set.Icc}\left((0: \mathbb{R}), 1\right), \lambda (T: \mathbb{R}) \mapsto (\operatorname{Real.log}\left(P\left(T\right)\right))\right))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.claim` (`✓ std3`).

*Citation.* Anaelle Hertz, Noah Lupu-Gladstein, Khabat Heshami, Aaron Z. Goldberg (2026). *Equalities and inequalities from entanglement, loss, and beam splitters*. DOI: [10.1007/s40509-026-00402-0](https://doi.org/10.1007/s40509-026-00402-0). URL: <https://arxiv.org/abs/2501.02047v1>.

*Commentary.*

Section III, Conjecture 7, asserts that the purity under loss is log-convex on [0,1]; equation (26) states the equivalent derivative inequality. Here k is any natural number, the real weights are nonnegative and sum to one, and every pure vector has norm one. The claim asks for the actual purity curve and convexity of its logarithm. Every finite ensemble represents a state, so the source's assertion for every state implies this finite-ensemble statement. ConvexOn includes both endpoints and requires no differentiability hypothesis.

**Theorem 1.4 (A three-level counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hertz-lupu-gladstein-heshami-goldberg-2025-loss-purity-log-convexity` (refuted) by `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hertz-lupu-gladstein-heshami-goldberg-2025-loss-purity-log-convexity","declaration_gid":"D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anaelle Hertz, Noah Lupu-Gladstein, Khabat Heshami, Aaron Z. Goldberg (2026). *Equalities and inequalities from entanglement, loss, and beam splitters*. DOI: [10.1007/s40509-026-00402-0](https://doi.org/10.1007/s40509-026-00402-0). URL: <https://arxiv.org/abs/2501.02047v1>.

*Commentary.*

Take the Fock-diagonal input diag(1/100,3/4,6/25), with zero population above level two. Binomial thinning gives diag(q_0,q_1,q_2), where q_0=1/100+(3/4)(1-T)+(6/25)(1-T)^2, q_1=(3/4)T+(12/25)T(1-T), and q_2=(6/25)T^2. Its purity is q_0^2+q_1^2+q_2^2=(1728T^4-8856T^3+17529T^2-12300T+5000)/5000.

At T=39/40, 49/50 and 197/200 the purity values are respectively 120972467/200000000, 4749230357/7812500000 and 76369391837/125000000000. The middle transmissivity is the midpoint of the other two. The square of its purity exceeds the product of the endpoint purities by 7296233469022569/15625000000000000000000. All three values are positive. Convexity of their logarithms would give the opposite weak inequality, so Conjecture 7 fails for this mixed state.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.IsPurityCurve`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.loss`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.result`
- Dependency: [D5/S3/Quantum/Measurement/PureLossIncompatibility](../../Measurement/PureLossIncompatibility.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy](Entropy.md)
