# Euler Windows Below the Completed Zero Reading

## Abstract

The prime-axis coordinate trace agrees with zeta in its convergence domain, while finite prime windows stay zero-free.

<a id="describe-the-prime-axis-heat-trace-is-the-coordinate-sum"></a>

**Definition 1.1 (The prime-axis heat trace is the coordinate sum).**

Lean statement: `D5/S3/Zeros/EulerWindows.primeAxisHeatTrace`

*Formalization.* `D5/S3/Zeros/EulerWindows.primeAxisHeatTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition sums the existing labeled-zeta coefficient over the repository's PrimeAxisTable. The table type and coefficient family already exist; this declaration proves neither convergence nor a spectral trace-class realization. `D5/L/hedenmalm1997hilbert` supplies the square-summable Dirichlet-series context, but the prime-axis encoding and heat-trace name are repository translations. This is the initial half-plane reading that an O-6 route must connect faithfully to completed zeta.

<a id="describe-the-prime-axis-heat-trace-equals-classical-zeta-in-the-absolute-half-plane"></a>

**Theorem 1.2 (The prime-axis heat trace equals classical zeta in the absolute half-plane).**

$\forall s\in\mathbb{C},\ 1<\Re(s) \Rightarrow \operatorname{primeAxisHeatTrace}(s)=\operatorname{classicalZeta}(s)$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/EulerWindows.prime_axis_heat_trace_eq_zeta` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

For real part strictly greater than one, the PrimeAxisTable coefficient sum is classical zeta. The half-plane hypothesis is explicit and supplies the convergence needed by the existing zeta-kernel theorem. Compared with the ingested definition, the checked statement uses the repository's established coefficient family and asserts no analytic continuation beyond this domain. It is the local-germ endpoint that continuation uniqueness can eventually join to the completed reading on the O-6 path.

<a id="describe-finite-prime-windows-have-no-zeros-at-positive-abscissa"></a>

**Theorem 1.3 (Finite prime windows have no zeros at positive abscissa).**

$$\forall S\subset_{\operatorname{fin}}\mathbb{N},\ (\forall p\in S,\ \operatorname{Prime}(p)) \Rightarrow \forall s\in\mathbb{C},\ 0<\Re(s) \Rightarrow \operatorname{finiteEulerProduct}(S,s)\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/EulerWindows.finite_euler_window_ne_zero` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

For a supplied finite set of natural numbers, a supplied proof that every member is prime, and a complex parameter with positive real part, the corresponding finite Euler product is nonzero. A finite set is always inhabited as a value, but it may be empty; no nonempty window is required. Compared with the ingested corollary, Lean proves only finite-window nonvanishing. It does not prove all-prime tail participation, critical-strip convergence failure, epsilon-readout necessity, window escape, or a continued-correlation interpretation. For O-6 this excludes finite Euler factors as the source of a projected zero while leaving the analytic tail and continuation obligations open.

## References

- Truth anchor: `D5/S3/Zeros/EulerWindows.finite_euler_window_ne_zero`
- Truth anchor: `D5/S3/Zeros/EulerWindows.primeAxisHeatTrace`
- Truth anchor: `D5/S3/Zeros/EulerWindows.prime_axis_heat_trace_eq_zeta`
