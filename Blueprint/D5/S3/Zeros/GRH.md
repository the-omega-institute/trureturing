# Zeros of the Riemann zeta function and Dirichlet L-functions

## Abstract

Zeros of the Riemann zeta function and Dirichlet L-functions

Levent Alpöge's proof, written with Claude, reaches the critical line through a nonvanishing theorem. In the compact edition, New.Main compares two bounds for the covolume of the same family of theta lifts. After the main height cancels, the comparison bounds a weighted prime sum from above. A one-sided analytic criterion converts the resulting estimate into nonvanishing for every Dirichlet character to the right of the critical line, with the principal character's pole excluded.

The functional equation then rules out a zero in the left half of the open critical strip by passing to the reflected point for the corresponding character. For the Riemann zeta function the proof specializes to modulus one and uses the functional equation for the completed zeta function. The negative even integers are among the poles of the classical gamma factor, and the zeta statement excludes them explicitly.

**Theorem 1.1 (The Riemann hypothesis).**

Lean statement: `D5/S3/Zeros/GRH.riemannHypothesis`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH.riemannHypothesis` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Every complex zero of the Riemann zeta function other than a negative even integer, with the point 1 excluded, has real part one half. The theorem supplies Mathlib's proposition RiemannHypothesis directly.

**Theorem 1.2 (The real part of a zeta zero).**

Lean statement: `D5/S3/Zeros/GRH.riemannZeta_eq_zero_re`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH.riemannZeta_eq_zero_re` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For a specified complex s, the hypotheses are that the zeta value at s vanishes, that s differs from −2(n + 1) for every natural number n, and that s differs from 1. The conclusion is Re(s) = 1/2.

**Theorem 1.3 (Nonvanishing in the open right half-plane).**

Lean statement: `D5/S3/Zeros/GRH.LFunction_ne_zero_of_half_lt_re`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH.LFunction_ne_zero_of_half_lt_re` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let the modulus be any positive integer, and let χ be any complex Dirichlet character of that modulus. For every complex s with Re(s) > 1/2, the value of L(s, χ) is nonzero if χ is nonprincipal or s differs from 1.

**Theorem 1.4 (All characters in the open critical strip).**

Lean statement: `D5/S3/Zeros/GRH.LFunction_eq_zero_re`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH.LFunction_eq_zero_re` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For every positive modulus and every complex Dirichlet character χ, if 0 < Re(s) < 1 and L(s, χ) = 0, then Re(s) = 1/2. This includes imprimitive characters.

**Theorem 1.5 (Primitive characters).**

Lean statement: `D5/S3/Zeros/GRH.LFunction_eq_zero_re_of_isPrimitive`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH.LFunction_eq_zero_re_of_isPrimitive` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Fix a primitive complex Dirichlet character χ of any positive modulus. Every complex zero s of L(s, χ) with 0 < Re(s) < 1 has Re(s) = 1/2. This follows by applying the theorem for all characters at χ.

## References

- Truth anchor: `D5/S3/Zeros/GRH.LFunction_eq_zero_re`
- Truth anchor: `D5/S3/Zeros/GRH.LFunction_eq_zero_re_of_isPrimitive`
- Truth anchor: `D5/S3/Zeros/GRH.LFunction_ne_zero_of_half_lt_re`
- Truth anchor: `D5/S3/Zeros/GRH.riemannHypothesis`
- Truth anchor: `D5/S3/Zeros/GRH.riemannZeta_eq_zero_re`
- Dependency: [D5/S3/Zeros/GRH/New/Main](GRH/New/Main.md)
