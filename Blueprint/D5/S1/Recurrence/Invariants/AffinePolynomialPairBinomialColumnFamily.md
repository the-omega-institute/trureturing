# The binomial column family of the affine pair

## Abstract

The column family h_d(m) = [z^m](1 + z)/(1 − z)^d has binomial closed forms, partial sums, a finite-difference recurrence and a reflection-symmetric polynomial extension.

**Definition 1.1 (The column family).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.h`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.h` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

h_d(m) is the integer coefficient of z^m in (1 + z)/(1 − z)^d, using Mathlib's inverse of (1 − z)^d.

**Definition 1.2 (The polynomial extension).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.H`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.H` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

H_d(t) = (2/(d − 1)!) (t + (d − 1)/2) ∏_{i=1}^{d−2} (t + i) in Q[t].

**Theorem 1.3 (Closed forms, sums, recurrence and symmetry).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

For d ≥ 2 and every m, h_d(m) = C(m + d − 1, d − 1) + C(m + d − 2, d − 1) = 2C(m + d − 1, d − 1) − C(m + d − 2, d − 2) = (2m + d − 1)/(d − 1) · C(m + d − 2, d − 2). For every d and m, h_{d+1}(m) = ∑_{j=0}^{m} h_d(j). For every d and every m ≥ 2, h_d(m) = ∑_{j=1}^{min(d, m)} (−1)^{j+1} C(d, j) h_d(m − j); the source states d ≥ 2 and m ≥ d, where min(d, m) = d. The bound m ≥ 2 is needed: h_1(1) = 2 while the right side is h_1(0) = 1. The condition d ≥ 2 is needed for the closed forms and for H_d: h_1(0) = 1 while the first closed form gives 2, and h_1 = 1, 2, 2, … is not a polynomial in m. For d ≥ 2, H_d agrees with h_d on every natural m, has degree d − 1 and leading coefficient 2/(d − 1)!, and H_d(−t − d + 1) = (−1)^{d−1} H_d(t) for every rational t. The partial sums come from 1/(1 − z)^{d+1} = 1/(1 − z)^d · 1/(1 − z), and the recurrence from (1 − z)^d (1 + z)/(1 − z)^d = 1 + z. The polynomial value uses C(m + d − 2, d − 2)(d − 2)! = (m + 1)⋯(m + d − 2), and the reflection reverses this product. This is Corollary 6 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281).

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.H`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.h`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily.result`
