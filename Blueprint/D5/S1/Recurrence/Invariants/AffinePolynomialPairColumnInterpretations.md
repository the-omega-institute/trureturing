# Interpretations of the binomial column family h_d

## Abstract

The column family h_d counts subsets meeting two blocks, diagonal queen placements, Chebyshev coefficients and lattice points of a dilated order polytope.

**Definition 1.1 (Board cells).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.cells`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.cells` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

The cells of an n × n board are the pairs (r, c) with 0 ≤ r, c < n.

**Definition 1.2 (Diagonal queen placements).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.queenPlacements`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.queenPlacements` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

The placements of k queens on an n × n board are the k-element sets of cells whose distinct members lie in distinct rows and columns with |r − r'| = |c − c'|.

**Definition 1.3 (Order polytope lattice points).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.orderPolytopePoints`

*Formalization.* `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.orderPolytopePoints` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

For the poset of a chain of k elements below two incomparable elements, the lattice points of the mth dilation of its order polytope are the weakly order-preserving labelings by 0, …, m: a weakly increasing labeling of the chain together with the labels of the two upper elements, each at least every chain label.

**Theorem 1.4 (Four interpretations).**

Lean statement: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28*. DOI: [10.5281/zenodo.24211281](https://doi.org/10.5281/zenodo.24211281). URL: <https://zenodo.org/records/24211281>.

*Commentary.*

Here h_d(m) = [z^m](1 + z)/(1 − z)^d. (1) Let X have m + d elements, Y ⊆ X two elements and Z ⊆ X. The number of d-subsets of X meeting both Y and Z equals h_d(m) exactly when d = 0, |Z| > m or Y ⊆ Z. (2) For d ≥ 4 there are 2h_d(m) placements of d − 2 queens on an (m + d − 2) × (m + d − 2) board in distinct rows and columns with every pair attacking diagonally. (3) For r ≥ 1, the coefficient of t^r in the Chebyshev polynomial T_{r+2m} is (−1)^m 2^{r−1} h_{r+1}(m). (4) For every k ≥ 0, the mth dilation of the order polytope of a chain of k elements below two incomparable elements has h_{k+3}(m) lattice points.

(1) Since (1 + z)/(1 − z)^d = (1 − z²)/(1 − z)^{d+1}, h_d(m) = C(m + d, d) − C(m + d − 2, d), the number of d-subsets meeting Y. When |Z| > m, every d-subset meets Z; when Y ⊆ Z, meeting Y implies meeting Z. Otherwise a d-subset of X \ Z through a point of Y \ Z meets Y but not Z. (2) Two attacking queens share a main or an anti-diagonal; three pairwise attacking queens in distinct rows share one line, so a placement lies on a single diagonal line. The main lines of an n × n board have lengths 1, …, n, …, 1, giving C(n, k + 1) + C(n + 1, k + 1) sets, and the reflection c ↦ n − 1 − c matches anti-diagonals with main diagonals. (3) The recurrence gives [t^r]T_{r+2m} = 2[t^{r−1}]T_{r−1+2m} − [t^r]T_{r+2m−2}, matching h_{r+1}(m) = h_r(m) + h_{r+1}(m − 1), with [t^r]T_r = 2^{r−1} and [t^0]T_{2m} = (−1)^m. (4) A chain bounded by t has C(t + k, k) labelings; summing over the two upper labels u, w with t = min(u, w) gives h_{k+3}(m).

The source assumes d ≥ 4 throughout, with Y and Z disjoint of sizes 2 and m + d − 3. That size exceeds m when d ≥ 4, and disjointness is not used. Queens need d ≥ 4: for d = 3 a single queen gives (m + 1)² placements, half of 2h_3(m) = 2(m + 1)². The Chebyshev identity needs r ≥ 1: [t^0]T_2 = −1, while (−1)·h_1(1) = −2. This is Corollary 8 of H. Ma and W. Zhang's note on A208509 (DOI 10.5281/zenodo.24211281), which attributes item 1 to Janjić's Theorem 1 and the four items to Liu–Xin–Zhang (Propositions 4.6–4.8 and Section 4.2).

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.cells`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.orderPolytopePoints`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.queenPlacements`
- Truth anchor: `D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnInterpretations.result`
- Dependency: [D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily](AffinePolynomialPairBinomialColumnFamily.md)
