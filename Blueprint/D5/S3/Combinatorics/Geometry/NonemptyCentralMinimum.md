# Minimum nonempty central graphs

## Abstract

A nonempty central graph on n ≥ 2 points has at least ⌈n/2⌉ edges, with equality exactly for the bicentral perfect matchings and their odd analogues.

**Definition 1.1 (The equality degrees).**

Lean statement: `D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum.EqualityDegrees`

*Formalization.* `D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum.EqualityDegrees` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

A graph on n points has the equality degrees when every degree is 1 and n is even, or when n is odd, one point has degree 2 and every other point has degree 1. These are the graphs (n/2)P₂ and P₃ ∪ ((n−3)/2)P₂: the two neighbours of the degree-2 point have degree 1, so they form a path on three points, and the rest is a perfect matching.

**Theorem 1.2 (The nonempty minimum and its equality graphs).**

Lean statement: `D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum.nonempty_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum.nonempty_minimum` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska Conjecture 4.2, arXiv:2610.11596v1, Section 4, p. 13: sharp bounds and corollaries of Petrov (2022) and Dovgoshey et al. (2026)*. DOI: [10.5281/zenodo.24369118](https://doi.org/10.5281/zenodo.24369118). URL: <https://doi.org/10.5281/zenodo.24369118>.

*Commentary.*

For n ≥ 2 the least number of edges of a nonempty central graph on n points is ⌈n/2⌉. One central edge of length t makes t central, so every point has a central neighbour and there are at least two central values; the edge-cover bound then gives ⌈n/2⌉ edges, and a bicentral space attains it. At equality the edge-cover bound forces exactly two central values, and the degrees, all at least 1, add up to 2⌈n/2⌉, which is n or n+1; so they are the equality degrees. Conversely, the band whose central pairs are the edges of such a graph realizes it as a central graph. Without the nonemptiness condition the minimum is 0 for n ≥ 3, by a one-central space. This is Corollary 8 of H. Ma and W. Zhang; the nonempty minimum is Theorem 3.10 of O. Dovgoshey and O. Rovenska, whose Theorem 3.12 printed the odd equality graph as P₃ ∪ hP₂ for n=2h+1 instead of P₃ ∪ (h−1)P₂.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum.EqualityDegrees`
- Truth anchor: `D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum.nonempty_minimum`
- Dependency: [D5/S3/Combinatorics/Geometry/CentralSizeEdgeMinima](CentralSizeEdgeMinima.md)
