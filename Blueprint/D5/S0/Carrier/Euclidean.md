# Golden Euclidean Division

## Theorem: Norm-Euclidean division

Provenance: `literature-attested` via `D5/L/chatland1949euclidean` (`lit/chatland1949euclidean`)

Statement: `D5/S0/Carrier/Euclidean.golden_division` `✓ std3`

For `a` and nonzero `b`, divide `a * conj(b)` by the nonzero integer `N(b)` and round both rational coordinates in the integral basis `(1, phi)`. Mathlib's nearest-integer operation makes the tie rule deterministic.

If the two coordinate errors are `x` and `y`, then each has absolute value at most `1/2`. Completing squares bounds `|x^2 + xy - y^2|` by `5/16`, so multiplicativity of the norm gives a remainder with strictly smaller absolute norm.

The `EuclideanDomain GoldenInt` instance uses this quotient and remainder with Euclidean relation `(N(r)).natAbs < (N(b)).natAbs`.
