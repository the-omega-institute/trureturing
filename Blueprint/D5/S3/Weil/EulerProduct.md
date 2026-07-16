# Euler Windows and Single-Address Heat

## Theorem: Finite Euler windows have only the local denominator lattice

Provenance: `literature-attested` via `D5/L/apostol1976introduction` (`lit/apostol1976introduction`)

Statement: `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus` `✓ std3`

A finite Euler product is nonzero exactly on the locus where every local denominator is nonzero, and the complementary denominator-zero locus is the union of the imaginary lattices indexed by its primes. Lean totalizes inversion with zero inverse equal to zero, so the zero-free clause is deliberately restricted to the regular locus; no pole order or numerical window certificate is asserted.

## Definition: The single-address reading is the von Mangoldt weight

Provenance: `literature-attested` via `D5/L/apostol1976introduction` (`lit/apostol1976introduction`)

Statement: `D5/S3/Weil/EulerProduct.single_address_reading_spec` `✓ std3`

Under the value map from a one-prime ledger state to a natural prime power, a nonzero exponent at p reads log p, while every non-prime-power value reads zero. This is the classical von Mangoldt coefficient in the repository's single-address coordinates.

## Proposition: The logarithmic derivative is the single-address heat trace

Provenance: `literature-attested` via `D5/L/apostol1976introduction` (`lit/apostol1976introduction`)

Statement: `D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative` `✓ std3`

In the convergence half-plane with real part greater than one, the L-series of the single-address reading equals minus the derivative of the classical zeta function divided by the zeta function. The statement adds no continuation beyond that half-plane.
