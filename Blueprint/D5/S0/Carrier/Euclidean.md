# Golden Euclidean Division

## Abstract

Nearest-coordinate division makes the golden integers norm-Euclidean.

**Theorem 1.1 (Norm-Euclidean division).**

$$\forall a,b\in\mathbb{Z}[\varphi],\ b\neq 0 \Rightarrow \exists q,r\in\mathbb{Z}[\varphi],\ a=qb+r \land (r=0 \lor \lvert\operatorname{norm}(r)\rvert<\lvert\operatorname{norm}(b)\rvert)$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Euclidean.golden_division` (`✓ std3`). ∎

*Citation.* H. Chatland (1949). *On the Euclidean algorithm in quadratic number fields*. DOI: [10.1090/S0002-9904-1949-09315-1](https://doi.org/10.1090/S0002-9904-1949-09315-1).

*Commentary.*

For `a` and nonzero `b`, divide `a * conj(b)` by the nonzero integer `N(b)` and round both rational coordinates in the integral basis `(1, phi)`. Mathlib's nearest-integer operation makes the tie rule deterministic.

If the two coordinate errors are `x` and `y`, then each has absolute value at most `1/2`. Completing squares bounds `|x^2 + xy - y^2|` by `5/16`, so multiplicativity of the norm gives a remainder with strictly smaller absolute norm.

The `EuclideanDomain GoldenInt` instance uses this quotient and remainder with Euclidean relation `(N(r)).natAbs < (N(b)).natAbs`.
