# Meromorphic horizontal lognorm transport

## Abstract

Compact meromorphic functions satisfy an exact signed horizontal lognorm transport identity.

Let a<=b and let u and v be arbitrary real heights. Let K be the closed rectangle with real part in [a,b] and imaginary part between min(u,v) and max(u,v). Suppose f is meromorphic on K and meromorphicOrderAt f z is not top for every z in K. the horizontal integral of log ||f|| at v minus the corresponding integral at u equals the signed height integral of the negative imaginary part of f'/f.

**Theorem 1.1 (Signed transport through every zero and pole height).**

Lean statement: `D5/S3/Analytic/Boundary/MeromorphicHorizontalLogTransport.meromorphic_horizontal_lognorm_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/MeromorphicHorizontalLogTransport.meromorphic_horizontal_lognorm_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof factors the meromorphic function on the compact rectangle into a finite signed divisor product and an analytic nonvanishing factor. The logarithm of each divisor factor is the real logarithm of a distance, and its quotient contribution is the corresponding real horizontal kernel with its integer multiplicity, including negative multiplicities. The analytic factor is handled by vertical differentiation and real Fubini. Codiscrete equality is restricted independently on every horizontal slice; the finite exceptional sets therefore disappear from the interval integrals. Every horizontal logarithm and imaginary-part slice is interval integrable, as is the outer signed integral. The theorem includes spatial endpoints, degenerate rectangles, zeros and poles on every height, and both orientations of the signed height interval. It does not assert the Riemann hypothesis or impose a zero-free, good-height, open-domain, or assumed integrability restriction.

The conclusion concerns finite signed interval integrals of real functions. It does not assert integrability of the complex logarithmic derivative on a singular slice. Global continuation, zeta identification and the Riemann hypothesis require separate results.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/MeromorphicHorizontalLogTransport.meromorphic_horizontal_lognorm_transport`
- Dependency: [D5/S3/Analytic/Boundary/HorizontalLogPotential](HorizontalLogPotential.md)
- Dependency: [D5/S3/Analytic/Boundary/LogNormDirectionalDerivative](LogNormDirectionalDerivative.md)
