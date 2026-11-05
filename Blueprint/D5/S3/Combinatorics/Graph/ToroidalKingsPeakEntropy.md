# The all-integer toroidal king peak-entropy limit

## Abstract

Toroidal king modal coefficients and the literal square-tiling growth constant.

The source is the conjecture in OEIS A394697 revision 24: a(n)^(1/n^2) tends to A247413. A247413 revision 41 identifies that constant as the limit of A063443(m)^(1/m^2), and A063443 revision 104 counts tilings by unit and two-by-two squares, equivalently free king boards of side m-1. The common OEIS data revision is 77073cc8105b8042be07ec0d885da5ea5960ff3c. The graph, full coefficient range, literal constant and all-integer quantifiers are retained.

**Definition 1.1 (Square-area root).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.rootGrowth`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.rootGrowth` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2026). *OEIS A394697: maximum coefficient of the toroidal king independence polynomial*. URL: <https://oeis.org/A394697>.

*Commentary.*

Cast a(n) to a real number and raise it to the reciprocal of n squared. This is the real exponent 1/n squared in the published question.

**Definition 1.2 (The source constant).**

Lean statement: `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.a247413`

*Formalization.* `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.a247413` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2026). *OEIS A394697: maximum coefficient of the toroidal king independence polynomial*. URL: <https://oeis.org/A394697>.

*Commentary.*

a247413 is limUnder atTop of rootGrowth(a063443). It is defined from the square-tiling sequence independently of toroidal counts. The proof establishes convergence of this exact sequence before identifying its limit.

**Theorem 1.3 (The complete convergence statement).**

$$\forall e \in \mathrm{Real},\; 0 < e \Rightarrow \left(\exists N \in \mathrm{Nat},\; 3 \le N \land \left(\forall n \in \mathrm{Nat},\; N \le n \Rightarrow \mathrm{abs}\left(\mathrm{sub}\left(\mathrm{rootGrowth}\left(\mathrm{peak}, n\right), \mathrm{a247413}\right)\right) < e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a394697-toroidal-king-peak-entropy` (proved) by `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a394697-toroidal-king-peak-entropy","declaration_gid":"D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2026). *OEIS A394697: maximum coefficient of the toroidal king independence polynomial*. URL: <https://oeis.org/A394697>.

*Commentary.*

For every positive real epsilon there is a natural N at least three such that, for every natural n at least N, the absolute difference between peak(n)^(1/n squared) and a247413 is less than epsilon. Empty seams give freeCount(n-1)<=torusCount(n)<=freeCount(n), while torusCount(n)<=(n squared plus one)*peak(n) and peak(n)<=torusCount(n). The shifted free logarithmic limit and the vanishing polynomial logarithmic loss squeeze log(peak(n))/n squared to the same value. Exponentiation and uniqueness of the separately defined tiling limit yield the stated literal constant. Both periodic coordinates, odd n, empty configurations and every cardinality from zero through n squared remain in scope.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.a247413`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy.rootGrowth`
- Dependency: [D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam](ToroidalKingsEmptySeam.md)
