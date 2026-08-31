# Second-Magnus Swap Curvature

## Abstract

An alternating Fourier slot kernel modulates finite holonomy into a bounded second-Magnus energy.

**Definition 1.1 (Second-Magnus Fourier slot kernel).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.secondMagnusSwapKernel`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.secondMagnusSwapKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel is the determinant obtained by assigning two frequency characters to two fixed time slots and subtracting the swapped assignment.

**Definition 1.2 (Finite second-Magnus energy).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.finiteSecondMagnusEnergy`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.finiteSecondMagnusEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each ordered-pair curvature is multiplied by its two-slot Fourier kernel, squared in norm, and summed over the finite carrier.

**Definition 1.3 (Stable residual second-Magnus energy).**

Lean statement: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.stableResidualSecondMagnusEnergy`

*Formalization.* `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.stableResidualSecondMagnusEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite second-Magnus construction is specialized to the existing stable residual swap-curvature field.

**Theorem 1.4 (Frequency-exchange antisymmetry).**

$$\forall f_{p}: \mathbb{R}, f_{q}: \mathbb{R}, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, \operatorname{secondMagnusSwapKernel}(f_{q}, f_{p}, t_{1}, t_{2}) = -\operatorname{secondMagnusSwapKernel}(f_{p}, f_{q}, t_{1}, t_{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_swap_frequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging the two frequency labels reverses the orientation and negates the slot kernel.

**Theorem 1.5 (Time-slot antisymmetry).**

$$\forall f_{p}: \mathbb{R}, f_{q}: \mathbb{R}, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, \operatorname{secondMagnusSwapKernel}(f_{p}, f_{q}, t_{2}, t_{1}) = -\operatorname{secondMagnusSwapKernel}(f_{p}, f_{q}, t_{1}, t_{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_swap_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging the two time slots reverses the orientation and negates the slot kernel.

**Theorem 1.6 (Equal-time vanishing).**

$$\forall f_{p}: \mathbb{R}, f_{q}: \mathbb{R}, t: \mathbb{R}, \operatorname{secondMagnusSwapKernel}(f_{p}, f_{q}, t, t) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_equal_times` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alternating determinant vanishes when both evaluations use the same time slot.

**Theorem 1.7 (Equal-frequency vanishing).**

$$\forall f: \mathbb{R}, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, \operatorname{secondMagnusSwapKernel}(f, f, t_{1}, t_{2}) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_equal_frequencies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alternating determinant vanishes when both channels carry the same frequency.

**Theorem 1.8 (Uniform kernel norm bound).**

$$\forall f_{p}: \mathbb{R}, f_{q}: \mathbb{R}, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, \left\lVert \operatorname{secondMagnusSwapKernel}(f_{p}, f_{q}, t_{1}, t_{2}) \right\rVert \leq 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_norm_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both phase products have unit norm, so their difference has norm at most two.

**Theorem 1.9 (Center and relative decomposition).**

$$\forall f_{p}: \mathbb{R}, f_{q}: \mathbb{R}, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, \operatorname{secondMagnusSwapKernel}(f_{p}, f_{q}, t_{1}, t_{2}) = \operatorname{fourierPhase}(\frac{f_{p} + f_{q}}{2}, t_{1} + t_{2}) \cdot (\operatorname{fourierPhase}(\frac{f_{p} - f_{q}}{2}, t_{1} - t_{2}) - \operatorname{fourierPhase}(-\frac{f_{p} - f_{q}}{2}, t_{1} - t_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_center_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mean time and mean frequency form a common unitary phase. The remaining bracket depends only on the time difference and half the frequency difference.

**Theorem 1.10 (Odd sine form).**

$$\forall f_{p}: \mathbb{R}, f_{q}: \mathbb{R}, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, \operatorname{secondMagnusSwapKernel}(f_{p}, f_{q}, t_{1}, t_{2}) = (-2i) \cdot \exp(-i \cdot (t_{1} + t_{2}) \cdot \frac{f_{p} + f_{q}}{2}) \cdot \sin((t_{1} - t_{2}) \cdot \frac{f_{p} - f_{q}}{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_sine_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative bracket is exactly minus two times the imaginary unit times the sine of half the time-frequency area, multiplied by the common mean phase.

**Theorem 1.11 (Finite energy domination).**

$$\forall f, c, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, 0 \leq \operatorname{finiteSecondMagnusEnergy}(f, c, t_{1}, t_{2}) \land \operatorname{finiteSecondMagnusEnergy}(f, c, t_{1}, t_{2}) \leq 4 \cdot \operatorname{finiteHolonomyEnergy}(c).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.finite_second_magnus_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite second-Magnus energy is nonnegative and bounded above by four times the underlying finite holonomy energy.

**Theorem 1.12 (Residual envelope to second-Magnus decay).**

$$\begin{gathered}\forall s, r, v, f, t_{1}: \mathbb{R}, t_{2}: \mathbb{R}, e: \mathbb{R}:\\{}(0 \leq e \land (\forall p, \left\lVert v_{p} \right\rVert \leq 1) \land (\forall p, \left\lVert r_{p} \right\rVert \leq e)) \Rightarrow\\{}0 \leq \operatorname{stableResidualSecondMagnusEnergy}(s, r, v, f, t_{1}, t_{2}) \land \operatorname{stableResidualSecondMagnusEnergy}(s, r, v, f, t_{1}, t_{2}) \leq 4 \cdot (\operatorname{card}(\iota)^{2} \cdot (2 \cdot \left\lVert s - 1 \right\rVert \cdot e + 2 \cdot e^{2})^{2}) \land\\{}(e = 0 \Rightarrow \operatorname{stableResidualSecondMagnusEnergy}(s, r, v, f, t_{1}, t_{2}) = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.stable_residual_second_magnus_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing finite energy domination with the stable residual holonomy bound makes a vanishing residual envelope sufficient for vanishing finite second-Magnus energy.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.finiteSecondMagnusEnergy`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.finite_second_magnus_energy_bound`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.secondMagnusSwapKernel`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_center_decomposition`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_equal_frequencies`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_equal_times`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_norm_le_two`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_sine_form`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_swap_frequency`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.second_magnus_swap_kernel_swap_time`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.stableResidualSecondMagnusEnergy`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.stable_residual_second_magnus_energy_bound`
- Dependency: [D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy](FiniteHolonomyEnergy.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle](TimeOrderedPrimeMemoryCocycle.md)
