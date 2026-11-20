# Companion coefficients and degrees of the affine polynomial pair

## Abstract

The companion polynomials u_n of the affine pair have coefficients C(n − 1, 2k) + C(n, 2k) − [k = 0], and deg v_n = ⌊(n − 1)/2⌋, deg u_n = ⌊n/2⌋.

**Theorem 1.1 (The companion formula and the two degrees).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairDegrees.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairDegrees.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

For every n ≥ 1, with u_n = first(pair(n − 1)) and v_n = second(pair(n − 1)), the coefficient of X^k in u_n is C(n − 1, 2k) + C(n, 2k) − [k = 0] for every k ≥ 0. Moreover both polynomials are nonzero, the degree of v_n is ⌊(n − 1)/2⌋ and that of u_n is ⌊n/2⌋. The coefficient formulas vanish beyond these indices, since both binomial coefficients are zero there and the constant-term correction does not apply. At the top index the coefficient C(n, 2k + 1), respectively C(n, 2k), is positive; for n = 1 the constant term of u_1 is one. This is Theorem 1 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281).

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairDegrees.result`
- Dependency: [D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients](AffinePolynomialPairBinomialCoefficients.md)
