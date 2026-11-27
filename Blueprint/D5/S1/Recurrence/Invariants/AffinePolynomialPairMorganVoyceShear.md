# The Morgan–Voyce shear of the affine pair

## Abstract

The Morgan–Voyce polynomials P_m have coefficients C(m + k, 2k) + 2C(m + k, 2k + 1), the sheared coefficients b_{m+k+1,k} of the affine pair.

**Definition 1.1 (The Morgan–Voyce polynomials).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear.P`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear.P` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

P_0 = 1, P_1 = 3 + x and P_m = (x + 2)P_{m−1} − P_{m−2} for m ≥ 2, in Z[x].

**Theorem 1.2 (The shear identity).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

For all m and k, [x^k]P_m = b_{m+k+1,k} = C(m + k, 2k) + 2C(m + k, 2k + 1), where b_{n,k} = [x^k] v_n is the coefficient of second(pair(n − 1)). Beyond k = m all three sides vanish, so the source range 0 ≤ k ≤ m is included. The binomial side satisfies the coefficient recurrence of P_m after two Pascal expansions, and Werner's formula with one Pascal step identifies it with b_{m+k+1,k}. This is Corollary 2 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281), André-Jeannin's r = 2 coefficient theorem.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear.P`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear.result`
- Dependency: [D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients](AffinePolynomialPairBinomialCoefficients.md)
