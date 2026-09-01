# Phase-Twisted Stable Swap Curvature

## Abstract

Unitary Fourier phases twist stable memory channels without worsening residual curvature-energy bounds.

**Definition 1.1 (Phase-twisted memory channel).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedChannel`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply a complex memory channel by the Fourier phase attached to its frequency at the chosen spectral time.

**Definition 1.2 (Phase-twisted stable swap curvature).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedStableSwapCurvature`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedStableSwapCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate stable residual swap curvature on the two phase-rotated memory channels.

**Definition 1.3 (Phase-twisted finite holonomy energy).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedStableHolonomyEnergy`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedStableHolonomyEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Aggregate the squared norms of all ordered-pair phase-twisted stable curvatures on a finite carrier.

**Theorem 1.4 (Unitary twisting preserves channel norm).**

$$\forall omega, t: \mathbb{R}, v: \mathbb{C},\\{}\left\lVert \operatorname{phaseTwistedChannel}(omega, t, v) \right\rVert = \left\lVert v \right\rVert.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_channel_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real frequency and spectral time, multiplying a complex channel by its Fourier phase preserves the channel norm.

The conclusion uses only the unit norm of the individual phase. It does not identify phases at different frequencies or assert phase synchronization.

**Theorem 1.5 (Relative frequency reconstructs channel phase).**

$$\forall omega_{p}, omega_{q}, t: \mathbb{R},\\{}\operatorname{fourierPhase}(omega_{p} - omega_{q}, t) \cdot \operatorname{fourierPhase}(omega_{q}, t) = \operatorname{fourierPhase}(omega_{p}, t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.relative_phase_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every spectral time, the phase at the difference of two real frequencies times the second phase equals the first phase.

This is the multiplicative character law for Fourier phases. It does not say that the two channel phases or their frequencies are equal.

**Theorem 1.6 (Logarithmic relative address phase).**

$$\forall n_{p}, n_{q}: \mathbb{N}, t: \mathbb{R},\\{}\operatorname{fourierPhase}(\operatorname{log}(n_{p}) - \operatorname{log}(n_{q}), t) \cdot \operatorname{logAddressPhase}(n_{q}, t) = \operatorname{logAddressPhase}(n_{p}, t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.relative_log_address_phase_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two natural-number addresses, the phase at the difference of their real logarithms reconstructs the first logarithmic address phase from the second.

The statement uses Lean's total real logarithm and assumes neither positivity nor primality of the addresses. It supplies no converse or address-identification result.

**Theorem 1.7 (Zero time recovers untwisted curvature).**

$$\forall a, r_{p}, r_{q}, v_{p}, v_{q}: \mathbb{C},\\{}omega_{p}, omega_{q}: \mathbb{R},\\{}\operatorname{phaseTwistedStableSwapCurvature}(a, r_{p}, r_{q}, v_{p}, v_{q}, omega_{p}, omega_{q}, 0) = \operatorname{stableResidualSwapCurvature}(a, r_{p}, r_{q}, v_{p}, v_{q}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_curvature_zero_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At spectral time zero, both Fourier twists are the identity, so the phase-twisted stable swap curvature equals the untwisted stable residual swap curvature.

This equality is restricted to zero time. It does not make curvature time-independent and gives no monotonicity or decay away from zero.

**Theorem 1.8 (Time-uniform pairwise residual curvature bound).**

$$\begin{gathered}\forall a, r_{p}, r_{q}, v_{p}, v_{q}: \mathbb{C},\\{}omega_{p}, omega_{q}, t: \mathbb{R},\\{}(\left\lVert v_{p} \right\rVert \leq 1 \land \left\lVert v_{q} \right\rVert \leq 1) \Rightarrow\\{}((\operatorname{phaseTwistedStableSwapCurvature}(a, r_{p}, r_{q}, v_{p}, v_{q}, omega_{p}, omega_{q}, t) = (a - 1) \cdot (r_{p} \cdot \operatorname{phaseTwistedChannel}(omega_{p}, t, v_{p}) - r_{q} \cdot \operatorname{phaseTwistedChannel}(omega_{q}, t, v_{q})) + r_{p} \cdot r_{q} \cdot (\operatorname{phaseTwistedChannel}(omega_{q}, t, v_{q}) - \operatorname{phaseTwistedChannel}(omega_{p}, t, v_{p}))) \land\\{}(\left\lVert \operatorname{phaseTwistedStableSwapCurvature}(a, r_{p}, r_{q}, v_{p}, v_{q}, omega_{p}, omega_{q}, t) \right\rVert \leq \left\lVert (a - 1) \right\rVert \cdot (\left\lVert r_{p} \right\rVert + \left\lVert r_{q} \right\rVert) + 2 \cdot \left\lVert r_{p} \right\rVert \cdot \left\lVert r_{q} \right\rVert) \land\\{}(\forall \varepsilon: \mathbb{R}, (0 \leq \varepsilon \land \left\lVert r_{p} \right\rVert \leq \varepsilon \land \left\lVert r_{q} \right\rVert \leq \varepsilon) \Rightarrow \left\lVert \operatorname{phaseTwistedStableSwapCurvature}(a, r_{p}, r_{q}, v_{p}, v_{q}, omega_{p}, omega_{q}, t) \right\rVert \leq 2 \cdot \left\lVert (a - 1) \right\rVert \cdot \varepsilon + 2 \cdot \varepsilon^{2})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_stable_swap_curvature_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming each of the two channel norms is at most one, the twisted curvature has the displayed linear-bilinear residual expansion and the corresponding pairwise norm bound.

For every nonnegative envelope bounding both residual norms, the stated quadratic envelope estimate follows uniformly in the chosen time. This norm estimate asserts no phase synchronization, time monotonicity, or residual decay.

**Theorem 1.9 (Time-uniform finite holonomy-energy bound).**

$$\begin{gathered}\forall \iota: \operatorname{Type}, [\operatorname{Fintype}(\iota)],\\{}a: \mathbb{C}, r, v: \iota \to \mathbb{C}, omega: \iota \to \mathbb{R},\\{}t, \varepsilon: \mathbb{R},\\{}(0 \leq \varepsilon \land (\forall p: \iota, \left\lVert v(p) \right\rVert \leq 1) \land (\forall p: \iota, \left\lVert r(p) \right\rVert \leq \varepsilon)) \Rightarrow\\{}\operatorname{let} E := \operatorname{phaseTwistedStableHolonomyEnergy}(a, r, v, omega, t),\\{}((0 \leq E) \land\\{}(E \leq \operatorname{card}_{\mathbb{R}}(\iota)^{2} \times (2 \times \left\lVert (a - 1) \right\rVert \times \varepsilon + 2 \times \varepsilon^{2})^{2}) \land\\{}((E = 0) \iff (\forall p, q: \iota, \operatorname{phaseTwistedStableSwapCurvature}(a, r(p), r(q), v(p), v(q), omega(p), omega(q), t) = 0)) \land\\{}(\varepsilon = 0 \Rightarrow E = 0)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_finite_holonomy_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite carrier, a nonnegative residual envelope together with the stated pointwise channel and residual bounds makes the twisted holonomy energy nonnegative and bounds it by the cardinality-square expression.

The energy is zero exactly when every ordered-pair twisted curvature vanishes, and a zero envelope forces zero energy. These finite, time-uniform facts imply no phase synchronization, residual decay, zero-location theorem, or RH conclusion.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedChannel`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedStableHolonomyEnergy`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phaseTwistedStableSwapCurvature`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_channel_norm`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_curvature_zero_time`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_finite_holonomy_energy_bound`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.phase_twisted_stable_swap_curvature_bound`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.relative_log_address_phase_reconstruction`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PhaseTwistedStableSwapCurvature.relative_phase_reconstruction`
- Dependency: [D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy](FiniteHolonomyEnergy.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow](PrimeFrequencyPhaseFlow.md)
