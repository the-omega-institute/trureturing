# The sharp four-central ultrametric minimum

## Abstract

A four-central ultrametric has at least eight points and at least 6n−16−4⌊n/4⌋+⌈n/2⌉ central edges, with length-by-length bounds and an attaining space for every n ≥ 8.

**Definition 1.1 (The attaining ultrametric).**

Lean statement: `D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum.FourTree`

*Formalization.* `D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum.FourTree` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska's central-edge conjectures: sharp bounds and tree corollaries*. DOI: [10.5281/zenodo.24389010](https://doi.org/10.5281/zenodo.24389010). URL: <https://doi.org/10.5281/zenodo.24389010>.

*Commentary.*

FourTree n is the point set {0,…,n−1} cut into the blocks {4k,…,4k+3} for k < ⌊n/4⌋, the last block absorbing the remaining n mod 4 points. The block {0,1,2,3} is one part and the other blocks form the second part. Each block is cut into its first two points and the rest; the points are grouped into the pairs {2k,2k+1} and, for odd n, the triple {n−3,n−2,n−1} with n−3 designated. Points in different parts are at distance 4, in different blocks of one part at 3, in different halves of one block at 2, in different components of one half at 3/2, at different positions of one component at 1, and the two undesignated points of the triple at 1/2. The distance depends only on the first level at which two points differ and decreases along the levels, so it is an ultrametric. For n ≥ 8 its center is {0,1,2,4}: the row of 0 takes only these values, and every point has a point at each of the distances 1, 2 and 4. The values 3, 3/2 and 1/2 are not central, since the point 0 is at none of them.

**Theorem 1.2 (The minimum and its length-by-length bounds).**

Lean statement: `D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum.ultra_four_central_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum.ultra_four_central_minimum` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Refuting Dovgoshey–Rovenska's central-edge conjectures: sharp bounds and tree corollaries*. DOI: [10.5281/zenodo.24389010](https://doi.org/10.5281/zenodo.24389010). URL: <https://doi.org/10.5281/zenodo.24389010>.

*Commentary.*

Let X be a finite ultrametric space with n points whose center has exactly four elements. Then n ≥ 8 and the central graph has at least 6n−16−4⌊n/4⌋+⌈n/2⌉ edges. Write the center as {0,a,b,D} with 0 < a < b < D. The central edges split by length; the length D has at least 4(n−4) edges, the length b at least 2n−4⌊n/4⌋ and the length a at least ⌈n/2⌉. For every n ≥ 8, FourTree n has four central values and exactly 6n−16−4⌊n/4⌋+⌈n/2⌉ central edges, so all three length bounds are attained at once.

The largest distance D is central and bounds every distance. For a point x, the points at distance below D from x include x, a point x′ at distance a, a point y at distance b and a point y′ at distance a from y; by the ultrametric inequality y′ is at distance b from x, so these four points are distinct. The class of a point and its complement therefore have at least four points each and are joined entirely at distance D, which gives at least |S|(n−|S|) ≥ 4(n−4) edges of length D and n ≥ 8.

The closed balls of radius b partition X. Inside a ball K, the points at distance below b from one of its points form a set U with at least two points, the rest K∖U also has at least two points, and every point of U is at distance b from every point of K∖U. Counting the points at distance b from each point of K gives at least 2|U||K∖U| ≥ 4|K|−8, so each ball has at least four points and there are at most ⌊n/4⌋ balls. Since the total count over all points is twice the number of edges of length b, there are at least 2n−4⌊n/4⌋ such edges. The length a has at least ⌈n/2⌉ edges because its edges cover every point.

The hypothesis of four central values is used for both lower lengths: without the value b the class bound drops to two points, which is the three-central case. This is Theorem 5 of H. Ma and W. Zhang (version 4), whose proof bounds the middle length by merging classes inside each ball; the Lean proof counts the incidences of length b from one class of each ball instead. O. Dovgoshey and O. Rovenska pose the central-edge problem in arXiv:2610.11596, Section 4. A structural characterization of the spaces attaining the minimum is not formalized; equality holds exactly when all three length bounds are attained, since they sum to the minimum.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum.FourTree`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Ultrametric/FourCentralMinimum.ultra_four_central_minimum`
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum](../UltrametricThreeCentralMinimum.md)
