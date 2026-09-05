# Euler Data to Arithmetic Prony Nodes

## Abstract

Von Mangoldt Euler data generate exact finite Prony traces. The meromorphically continued logarithmic derivative then maps each stored zeta-zero pole to a golden Prony node with its multiplicity-derived residue weight.

**Theorem 1.1 (Golden Euler nodes equal standard Mellin characters).**

$$\forall a, 0 < a \Rightarrow \forall s, \operatorname{eulerMellinPronyNode}(a, s) = a^{-s}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.euler_mellin_prony_node_eq_cpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive integer address, the golden exponential of its normalized logarithmic coordinate is exactly the complex power n raised to minus the Mellin step.

At unit step this specializes to the reciprocal integer node, while prime-power weights specialize through the canonical von Mangoldt formula.

**Theorem 1.2 (Finite von Mangoldt shift windows are exact Prony traces).**

$$\forall a, \forall b, \forall s, \forall t, \operatorname{finiteEulerShiftTrace}(a, b, s, t) = \operatorname{crystalTimeSample}(k \mapsto \operatorname{eulerMellinPronyNode}(a(k), s), k \mapsto \operatorname{eulerMellinPronyWeight}(a(k), b), t).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.finite_euler_shift_trace_eq_prony` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sampling a finite von Mangoldt Dirichlet window along an arithmetic progression in the Mellin parameter factors into fixed base weights and powers of fixed Euler nodes.

The right-hand side uses the repository's frozen crystal-time readout, so this bridge introduces no duplicate moment or delay-coordinate API.

**Theorem 1.3 (The Prony trace is the finite von Mangoldt Dirichlet window).**

$$\begin{gathered}\forall a, (\forall k, 0 < a(k)) \Rightarrow \forall b, \forall s, \forall t,\\{}\operatorname{finiteEulerShiftTrace}(a, b, s, t) = \sum_{k} \operatorname{vonMangoldt}(a(k)) \cdot a(k)^{-(b + t \cdot s)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.finite_euler_shift_trace_eq_vonMangoldt_dirichlet_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive addresses, the same finite trace is written directly with the standard arithmetic terms Lambda(n) times n raised to the shifted negative Mellin parameter.

This identifies the formal Prony nodes with genuine Euler characters rather than free spectral parameters.

**Theorem 1.4 (The continued Euler trace agrees with the von Mangoldt series).**

$$\forall s, 1 < \operatorname{re}(s) \Rightarrow \operatorname{continuedEulerTrace}(s) = \operatorname{singleAddressHeatTrace}(s).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.continued_euler_trace_eq_single_address_heat_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On real part greater than one, the negative logarithmic derivative of zeta is exactly the repository's von Mangoldt L-series.

The logarithmic derivative supplies the canonical continuation used to locate the zero-side pole centers.

**Theorem 1.5 (Zeta multiplicity becomes the Euler-pole residue).**

$$\begin{gathered}\forall r, \forall m, \operatorname{hasZetaZeroMultiplicity}(r, m) \Rightarrow\\{}\exists u, \operatorname{analyticAt}(u, r) \land u(r) \neq 0 \land\\{}\operatorname{eventuallyEqNearPunctured}(r, continuedEulerTrace, z \mapsto -\frac{m}{z - r} - \operatorname{logDeriv}(u, z)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.continued_euler_trace_principal_part` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analytic-unit factorization of a multiplicity-m zeta zero gives the punctured-neighborhood principal part minus m divided by s minus rho.

The regular remainder is the logarithmic derivative of the analytic unit. Thus the pole center and residue weight are both arithmetic data.

**Theorem 1.6 (Every stored Euler pole yields an actual golden Prony node).**

$$\begin{gathered}\forall Z, \forall n,\\{}(\exists u, \operatorname{analyticAt}(u, \operatorname{zero}(Z, n)) \land u(\operatorname{zero}(Z, n)) \neq 0 \land\\{}\operatorname{eventuallyEqNearPunctured}(\operatorname{zero}(Z, n), continuedEulerTrace, z \mapsto \frac{\operatorname{zeroDataEulerPoleWeight}(Z, n)}{z - \operatorname{zero}(Z, n)} - \operatorname{logDeriv}(u, z))) \land\\{}\operatorname{zeroDataZetaPronyNode}(Z, n) \neq 0 \land \operatorname{zeroDataZetaPronyNode}(Z, \operatorname{reflection}(Z, n)) = \operatorname{zeroDataZetaPronyNode}(Z, n)^{-1} \land\\{}(\operatorname{norm}(\operatorname{zeroDataZetaPronyNode}(Z, n)) = 1 \iff \operatorname{re}(\operatorname{zero}(Z, n)) = criticalAbscissa).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.zero_data_euler_pole_golden_prony_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each canonical ZeroData entry carries a continued-Euler principal part, a nonzero golden exponential node, and a multiplicity-derived residue weight.

Stored reflection inverts the node, and unit radius is equivalent to that zero lying on the critical line.

**Theorem 1.7 (Separated zero-pole nodes have exact finite observability).**

$$\forall Z, \forall j, \operatorname{Injective}(k \mapsto \operatorname{zeroDataZetaPronyNode}(Z, j(k))) \Rightarrow \operatorname{Injective}(\operatorname{firstCrystalTimeWindow}(k \mapsto \operatorname{zeroDataZetaPronyNode}(Z, j(k)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.finite_zeta_pole_prony_window_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite family of distinct continued-Euler pole nodes is exactly observable from the first matching number of Prony moments through the frozen Vandermonde theorem.

Node injectivity remains an explicit premise because one exponential sampling period can alias vertically separated frequencies.

## References

- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.continued_euler_trace_eq_single_address_heat_trace`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.continued_euler_trace_principal_part`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.euler_mellin_prony_node_eq_cpow`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.finite_euler_shift_trace_eq_prony`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.finite_euler_shift_trace_eq_vonMangoldt_dirichlet_window`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.finite_zeta_pole_prony_window_injective`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.zero_data_euler_pole_golden_prony_realization`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge](../../ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.md)
- Dependency: [D5/S3/Weil/EulerProduct](../EulerProduct.md)
- Dependency: [D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate](GoldenExponentialPronyCoordinate.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RhLocatesZeroData](../ZetaBridge/RhLocatesZeroData.md)
