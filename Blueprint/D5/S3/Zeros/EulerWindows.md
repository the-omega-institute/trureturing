# Euler Windows Below the Completed Zero Reading

## Definition: The prime-axis heat trace is the coordinate sum

Provenance: `repo-derived`

Statement: `D5/S3/Zeros/EulerWindows.primeAxisHeatTrace` `✓ std3`

The definition sums the existing labeled-zeta coefficient over the repository's PrimeAxisTable. The table type and coefficient family already exist; this declaration proves neither convergence nor a spectral trace-class realization. `D5/L/hedenmalm1997hilbert` supplies the square-summable Dirichlet-series context, but the prime-axis encoding and heat-trace name are repository translations. This is the initial half-plane reading that an O-6 route must connect faithfully to completed zeta.

## Theorem: The prime-axis heat trace equals classical zeta in the absolute half-plane

Provenance: `literature-attested` via `D5/L/hedenmalm1997hilbert` (`lit/hedenmalm1997hilbert`)

Statement: `D5/S3/Zeros/EulerWindows.prime_axis_heat_trace_eq_zeta` `✓ std3`

For real part strictly greater than one, the PrimeAxisTable coefficient sum is classical zeta. The half-plane hypothesis is explicit and supplies the convergence needed by the existing zeta-kernel theorem. Compared with the ingested definition, the checked statement uses the repository's established coefficient family and asserts no analytic continuation beyond this domain. It is the local-germ endpoint that continuation uniqueness can eventually join to the completed reading on the O-6 path.

## Theorem: Finite prime windows have no zeros at positive abscissa

Provenance: `literature-attested` via `D5/L/apostol1976introduction` (`lit/apostol1976introduction`)

Statement: `D5/S3/Zeros/EulerWindows.finite_euler_window_ne_zero` `✓ std3`

For a supplied finite set of natural numbers, a supplied proof that every member is prime, and a complex parameter with positive real part, the corresponding finite Euler product is nonzero. A finite set is always inhabited as a value, but it may be empty; no nonempty window is required. Compared with the ingested corollary, Lean proves only finite-window nonvanishing. It does not prove all-prime tail participation, critical-strip convergence failure, epsilon-readout necessity, window escape, or a continued-correlation interpretation. For O-6 this excludes finite Euler factors as the source of a projected zero while leaving the analytic tail and continuation obligations open.
