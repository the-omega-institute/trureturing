# Prime channels of the scaled golden candidate

## Abstract

GoldenCandidateOrbit

**Theorem 1.1 (The prime-three candidate lies inside the golden window).**

$$\left(\frac{1}{2 \times \varphi^{3}} < \operatorname{goldenCandidateOrbit}\left(3\right) \land \operatorname{goldenCandidateOrbit}\left(3\right) < \frac{1}{\varphi^{2}}\right) \land \operatorname{goldenCandidateOrbit}\left(5\right) < \frac{1}{2 \times \varphi^{3}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenCandidateOrbit.gc_orbit_two_prime_straddle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplier c is the fixed complex candidate of GermZeroCertificateReduction, whose real part lies in the certified prime-two golden window. Define goldenCandidateOrbitScale(p) = log(2)/log(p) and goldenCandidateOrbit(p) = goldenCandidateOrbitScale(p) * c.re for a prime p. The theorem places the prime-three value strictly between 1/(2*phi^3) and 1/phi^2, and the prime-five value strictly below the lower boundary.

This is an exact arithmetic location result for this fixed candidate. The independent universal local-factor scaling theorem is available in `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling`. A location statement for c does not assert that c or any transported candidate is a local-factor zero, and it gives no RH conclusion.

**Theorem 1.2 (Exactly primes two and three lie inside the window).**

$$\forall p \in \operatorname{Primes}\left(\mathbb{N}\right),\; \left(\frac{1}{2 \times \varphi^{3}} < \operatorname{goldenCandidateOrbit}\left(p\right) \land \operatorname{goldenCandidateOrbit}\left(p\right) < \frac{1}{\varphi^{2}}\right) \Leftrightarrow \left(\operatorname{val}\left(p\right) = 2 \lor \operatorname{val}\left(p\right) = 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/GoldenCandidateOrbit.scaled_gc_orbit_window_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p : Nat.Primes, the logarithmically scaled real part lies in the open golden window if and only if p.val = 2 or p.val = 3. There is no bound on p and no additional numerical premise. Primality excludes four; logarithm monotonicity and 2^9 < 5^4 exclude every prime at least five. The prime-three part uses the preceding straddle theorem, and the prime-two part uses the existing c_in_golden_window supplier.

The estimates compare logarithms of positive real numbers. The inequalities log(3) < 2*log(2), (9/4)*log(2) < log(5), and 2 < 2*phi^3*c.re < 9/4 locate the prime-three and prime-five values. Logarithm monotonicity then excludes every prime at least five.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenCandidateOrbit.gc_orbit_two_prime_straddle`
- Truth anchor: `D5/S3/Analytic/EulerGerm/GoldenCandidateOrbit.scaled_gc_orbit_window_iff`
- Dependency: [D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling](LocalFactorUniversalScaling.md)
- Dependency: [D5/S3/Analytic/GermWindow/GermZeroCertificateReduction](../GermWindow/GermZeroCertificateReduction.md)
- Narrative reference: [D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling](LocalFactorUniversalScaling.md)
