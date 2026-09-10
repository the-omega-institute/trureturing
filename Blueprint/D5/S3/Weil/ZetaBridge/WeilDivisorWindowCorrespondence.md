# Divisor Window Correspondence

## Abstract

The actual divisor carrier gives the canonical arithmetic Mellin window exactly up to its explicit missing-divisor function, with the complete prime-action correction retained.

**Definition 1.1 (Independent synthesis over the actual divisors).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisorWindow`

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisorWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use Nat.divisors, the same finite arithmetic carrier appearing in the 5040 divisor-partition research. On [-a,a], synthesize 4*exp(x/2)*sum_{d divides N} h(d*exp(x)), and extend by zero. This is a function on the original logarithmic window, not a newly named scalar partition or Fourier transform.

**Definition 1.2 (Complete arithmetic defect on the visible prefix).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.missingDivisorWindow`

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.missingDivisorWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum over every positive d<=M that does not divide N, using the same support, seed and half-density. Missing terms are combined as complex functions before taking any norms. No sign or positivity is assumed.

**Theorem 1.3 (Exact function-level dictionary including the remainder).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_exact_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_exact_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N nonzero, exp(2a)<=M, and a complex seed vanishing above exp(a), prove divisorWindow=windowMellinSum-missingDivisorWindow at every real point. Divisors beyond M vanish by the actual seed support. The remaining finite divisor set is identified with the divisibility filter of the original prefix. Coverage is not an assumption of this theorem.

**Theorem 1.4 (Original prime action with the missing-divisor correction).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_prime_action`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_prime_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing prime_forward_mellin_identity to the original window, and transport the exact function-level defect through the independently defined primeForward. Retain the log-seed defect, coordinate-times-defect, and prime action on the defect. This connects divisor data to the actual Lambda(n)/sqrt(n) translations without assuming Robin positivity or suppressing missing prime powers.

**Theorem 1.5 (Finite arithmetic coverage discharges the defect).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_prefix_correspondence`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_prefix_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every positive d<=M divides N, the actual missing-divisor set is empty, hence the two independently specified functions agree. The condition is on integer divisibility, not a supplied operator or Fourier identification.

**Theorem 1.6 (5040 and 2520 realize the same small window).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_windows_5040_and_2520`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_windows_5040_and_2520` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For exp(2a)<=10 and any supported complex seed, both 5040 and 2520 realize the original window with cutoff 10. All ten divisor checks are discharged in the proof. This is a shared finite-window function, although the scalar reciprocal-divisor sums differ.

The sharper L2 threshold exp(2a)<=11, the compressed-translation Euler product and its logarithmic derivative, and the origin-normalized genuine-ground/prolate numerical comparison are separately proved on paper in RH_RESEARCH_LANE_THEORY.md. Equality at the sharper threshold uses a null endpoint and is not claimed by the pointwise Lean theorem. Lean elaboration, Scribe emission and the transitive axiom audit have not run. No scalar Robin estimate is promoted to full Weil positivity, a spectral gap, or an unbounded-scale Xi limit.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisorWindow`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_exact_defect`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_prefix_correspondence`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_window_prime_action`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.divisor_windows_5040_and_2520`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.missingDivisorWindow`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining](WeilMellinPrimeIntertwining.md)
