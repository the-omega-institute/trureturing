# Row sums and alternating row sums of the affine polynomial pair

## Abstract

The affine polynomial pair has row sums v_n(1) = 3 · 2^{n−2} and u_n(1) = 3 · 2^{n−2} − 1 for n ≥ 2, and alternating row sums with a quadratic generating denominator.

**Definition 1.1 (The alternating row sums).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums.w`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums.w` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

w_n = v_n(−1) = second(pair(n − 1)) evaluated at −1, for the source index n ≥ 1.

**Theorem 1.2 (Row sums and the alternating recurrence).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

For every n ≥ 2, v_n(1) = 3 · 2^{n−2} and u_n(1) = 3 · 2^{n−2} − 1, while v_1(1) = u_1(1) = 1. In Z[[z]], (∑_{n≥1} w_n z^{n−1})(1 − 2z + 2z²) = 1 + z; w_{n+2} = 2w_{n+1} − 2w_n for n ≥ 1, w_1 = 1 and w_2 = 3. Evaluating the recursion at x = 1 gives u' = u + v and v' = u + v + 1, and induction from u_2(1) = 2, v_2(1) = 3 gives the doubling. At x = −1, eliminating u from u' = u − v and v' = u + v + 1 gives the second-order recurrence, which fixes every coefficient of the series product. This is Corollary 5 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281).

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums.w`
- Dependency: [D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients](AffinePolynomialPairBinomialCoefficients.md)
