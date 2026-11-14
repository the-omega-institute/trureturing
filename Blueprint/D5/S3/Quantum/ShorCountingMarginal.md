# Actual padded modular counting-register marginal

## Abstract

Actual padded modular counting-register marginal

**Theorem 1.1 (Actual-input counting marginal).**

$$\forall c \in \mathit{Parameters},\; \forall n \in \mathit{Nat},\; \forall y \in \operatorname{Fin}\left(2^{n}\right),\; \operatorname{sum}\left(t, \operatorname{Fin}\left(\operatorname{dimension}\left(c\right)\right), \operatorname{normSq}\left(\operatorname{runQPEAt}\left(\operatorname{modularOperator}\left(c\right), n, \operatorname{input}\left(c\right), y, t\right)\right)\right) = \frac{1}{\operatorname{period}\left(c\right)} \cdot \operatorname{sum}\left(s, \operatorname{Fin}\left(\operatorname{period}\left(c\right)\right), \operatorname{probability}\left(2^{n}, \frac{\operatorname{val}\left(s\right)}{\operatorname{period}\left(c\right)}, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorCountingMarginal.shor_qpe_probability_mixture` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

The target input is the computational basis vector at coordinate one. Multiplication by the coprime base permutes residues below the modulus and fixes padding. The control width n and target width are independent. The left side sums squared complex coordinate norms over every target coordinate at the specified counting outcome. The right side is the uniform mixture over all order eigenphases. No divisibility of the period into the power-of-two control dimension is assumed.

**Theorem 1.2 (Normalization over all counting outcomes).**

$$\forall c \in \mathit{Parameters},\; \forall n \in \mathit{Nat},\; \operatorname{sum}\left(y, \operatorname{Fin}\left(2^{n}\right), \operatorname{sum}\left(t, \operatorname{Fin}\left(\operatorname{dimension}\left(c\right)\right), \operatorname{normSq}\left(\operatorname{runQPEAt}\left(\operatorname{modularOperator}\left(c\right), n, \operatorname{input}\left(c\right), y, t\right)\right)\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorCountingMarginal.shor_distribution_normalized` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

Summing the actual marginal over all counting outcomes gives one, including n equal to zero. The proof consumes the actual-input mixture and the normalized phase kernels. It does not condition on a target-register measurement.

**Theorem 1.3 (Pointwise circular nearest-grid marginal bound).**

$$\forall c \in \mathit{Parameters},\; \forall n \in \mathit{Nat},\; \forall s \in \operatorname{Fin}\left(\operatorname{period}\left(c\right)\right),\; \forall b \in \operatorname{Fin}\left(2^{n}\right),\; \operatorname{Nearest}\left(2^{n}, \frac{\operatorname{val}\left(s\right)}{\operatorname{period}\left(c\right)}, b\right) \Rightarrow \frac{1}{\operatorname{period}\left(c\right)} \cdot \frac{4}{\mathit{pi}^{2}} \le \operatorname{sum}\left(t, \operatorname{Fin}\left(\operatorname{dimension}\left(c\right)\right), \operatorname{normSq}\left(\operatorname{runQPEAt}\left(\operatorname{modularOperator}\left(c\right), n, \operatorname{input}\left(c\right), b, t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorCountingMarginal.shor_mixture_peak_lower_bound` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

For any selected order eigenphase and any grid label within circular distance one over twice the control dimension, the actual marginal is at least one over the period times four over pi squared. Either midpoint tie is allowed. Distinct selected phases can share a grid label, so this pointwise result alone is not an aggregate-event success theorem.

**Theorem 1.4 (Arbitrary-phase circular nearest-outcome probability).**

$$\forall N \in \mathit{Nat},\; 0 < N \Rightarrow \left(\forall theta \in \mathit{Real},\; \forall b \in \operatorname{Fin}\left(N\right),\; \operatorname{Nearest}\left(N, \mathit{theta}, b\right) \Rightarrow \frac{4}{\mathit{pi}^{2}} \le \operatorname{probability}\left(N, \mathit{theta}, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorCountingMarginal.qpe_arbitrary_phase_lower_bound` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

QuantumPhaseEstimationGeneral.qpe_arbitrary_phase_lower_bound has exactly the explicit arguments N : Nat, hN : 0 < N, theta : Real, b : Fin N, and hnear : Nearest N theta b, in that order. Its conclusion is 4 / Real.pi squared less than or equal to probability N theta b. There is no restriction of theta to a chosen unit interval and no divisibility hypothesis. N can be any positive natural number; the actual counting circuit above specializes N to Q equal to two to the control width.

Nearest N theta b means that there exists an integer z with absolute value of theta minus b.val / N minus z at most 1 / (2 N). All divisions here are in the reals after casting natural and integer values. This is distance on the circle of phases measured in turns, so a label near the zero-one boundary is included and both labels at a midpoint tie satisfy the non-strict condition. The theorem is conditional on this relation for the supplied b; it is not a unique-choice assertion.

The amplitude is (1 / N) times the sum over k : Fin N of exp(2 pi i k.val (theta - b.val / N)), and probability is the squared complex norm of that amplitude. The factor 1 / N is the product of the inverse square-root normalization from uniform control preparation and that from the inverse Fourier map. The proof shifts theta by the integer z, uses periodicity of the amplitude, and squares the local norm bound 2 / pi. At an exactly integral phase difference the amplitude is one; the local estimate also covers that case.

For an order eigenphase take theta equal to s.val / r with s : Fin r and r equal to c.period, and N equal to Q = 2^n. Positivity holds also at n = 0, where Q = 1. The helper then gives the per-eigenphase nearest-outcome probability at least 4 / pi squared. The actual-input mixture above gives each component weight 1 / r; its complete target-register marginal therefore has the pointwise bound (1 / r) times 4 / pi squared. No condition r divides Q is used. These are distinct probabilities, and the Fourier output-reflection convention below applies when comparing their grid labels with Chapter 15.

Chapter 15 correspondence: Q is two to the control width; D is two to the independently chosen target width; r is the multiplicative order of the base modulo the modulus. Fin Q and ZMod Q are related by the pinned ZMod.finEquiv ring equivalence, using the least nonnegative representative. The modulus is at least two, the base is coprime to it, and the modulus fits in D. The supplied period positivity follows from coprimality.

The sums displayed here use sum(i, Fin m, f) for summation over the indicated finite index, and runQPEAt for coordinate evaluation of runQPE. The normalized positive Fourier transform in Chapter 15 is scale Q times the unnormalized negative-exponent ZMod.dft at the negated output coordinate. The supplied inverseQFT is scale Q times that DFT at the unreflected output. Thus using the positive transform for the final sweep reflects the grid label. At an output b satisfying the supplied circular nearest-grid condition for s/r, the positive final Fourier map has the same target vector at finEquiv.symm applied to negative finEquiv(b); the same pointwise bound holds at that reflected label. A sign change cannot be dropped. The uniform control preparation and final Fourier map each contribute an inverse square-root factor, giving the inverse-Q amplitude prefactor.

The actual circuit state is runQPE c.modularOperator n c.input. Its input has amplitude one precisely at target label one and zero elsewhere. At a fixed output y the complete target sum is normSquared of that target vector, and summing over y is the normalized distribution. registerPerm is the residue permutation extended by identity to the padding; no arbitrary joint state or conditioned posterior comb is substituted.

The marginal, normalization and pointwise circular nearest-grid estimate are the supported mathematical scope. Aggregate success probability, coprime sampling, continued-fraction recovery, factoring, gate or bit complexity, arbitrary control dimensions, conditioned posterior-comb bounds and hardware claims require separate results.

## References

- Truth anchor: `D5/S3/Quantum/ShorCountingMarginal.qpe_arbitrary_phase_lower_bound`
- Truth anchor: `D5/S3/Quantum/ShorCountingMarginal.shor_distribution_normalized`
- Truth anchor: `D5/S3/Quantum/ShorCountingMarginal.shor_mixture_peak_lower_bound`
- Truth anchor: `D5/S3/Quantum/ShorCountingMarginal.shor_qpe_probability_mixture`
