# The alternating affine pair and its polar angle

## Abstract

The alternating sums a_m = v_{m+1}(−1) of the affine pair satisfy a_m + i b_m = (1 + 2i)(1 − i)^m and have a continuous polar form.

**Definition 1.1 (The alternating pair).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.ab`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.ab` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

(a_0, b_0) = (1, 2) and (a_{m+1}, b_{m+1}) = (a_m + b_m, b_m − a_m).

**Definition 1.2 (The first component).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.a`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.a` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

a_m, the first component.

**Definition 1.3 (The second component).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.b`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.b` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

b_m, the second component.

**Theorem 1.4 (Complex form, four-step law and polar form).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

With the zero-based index m: a_m = v_{m+1}(−1); a_m + i b_m = (1 + 2i)(1 − i)^m; a_{m+4} = −4a_m and b_{m+4} = −4b_m; b_0, …, b_3 = 2, 1, −2, −6 and b_18 = −512. With α = arctan 2 and the continuous angle θ_m = α − mπ/4, a_m = A B^{θ_m} cos θ_m and b_m = A B^{θ_m} sin θ_m, where A = √5 · 16^{α/(2π)} and B = 16^{−1/(2π)}. Finally u_n(−1) = a_n − a_{n−1} − 1 for n ≥ 1. Multiplication by 1 − i gives the recurrences, and (1 − i)^4 = −4. A B^{θ_m} = √5 · 16^{m/8}, which grows by 16^{1/8} = √2 per step while θ decreases by π/4; with cos α = 1/√5 and sin α = 2/√5 an induction gives the polar form. The identification a_m = v_{m+1}(−1) uses the frozen recurrence w_{n+2} = 2w_{n+1} − 2w_n. This is Corollary 9 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281); the paper reports that it corrects the b-prefix and the polar branch recorded in A090131.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.ab`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.b`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar.result`
- Dependency: [D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums](AffinePolynomialPairRowSums.md)
