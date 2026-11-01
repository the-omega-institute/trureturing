# Occupancy means on a finite path

## Abstract

The occupancy means of binary words with no adjacent ones form the polytope defined by coordinate bounds and adjacent-sum inequalities. In three coordinates this is a square-based pyramid.

**Theorem 1.1 (The path stable set polytope).**

$$\operatorname{conv}\left(W_{n}\right) = P_{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_vertices` (`✓ std3`). ∎

*Citation.* Vaclav Chvatal (1975). *On certain polytopes associated with graphs*. URL: <https://doi.org/10.1016/0095-8956(75)90041-6>.

*Commentary.*

For every natural number n, a vector is a convex mixture of admissible binary words exactly when each coordinate lies in [0,1] and each adjacent pair sums to at most one. The empty path is included. For a single vertex, the coordinate upper bound is essential.

**Theorem 1.2 (The three-coordinate pyramid).**

$$x = (1-t) (u,0,v) + t (0,1,0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_three_pyramid` (`✓ std3`). ∎

*Citation.* Wikipedia contributors (2026). *Perfect graph — polyhedral characterization*. URL: <https://en.wikipedia.org/wiki/Perfect_graph>.

*Commentary.*

For three coordinates, nonnegativity and the two adjacent-sum inequalities already imply the coordinate upper bounds. Every point is a mixture of (u,0,v), with u and v in [0,1], and the apex (0,1,0). The mixing coefficient t is the middle occupancy x1. Thus the base is the unit square in the plane x1=0 and the apex has x1=1.

The induction keeps the entire tail mixture. On each tail word it prepends either zero or the complement of the first tail bit. At the level of means these are the affine maps y mapped to (0,y) and (1-y0,y). If x1 is below one, set t=x0/(1-x1); their mixture with coefficient t has the prescribed mean x. If x1 is one, x0 is zero and the first map suffices. A tail component of weight p therefore gives two components of weights (1-t)p and tp, preserving all tail correlations.

Write P_n for the same polytope and keep the same occupancy and Adm definitions. For natural n and k and an integer vector q indexed by Fin n, the real vector q belongs to the set scalar image k times P_n exactly when it is a sum of k occupancy vectors of admissible words, indexed by Fin k. Repeated words and empty layers are allowed. This is a derived application of the coordinate inequalities, convexHull_vertices, the public no-adjacent-true characterization AdmissibleCount.adm_iff_no_adjacent_true, and finite prefix and complement counting.

For positive k, scalar-image membership is equivalent to the integer bounds 0 <= q_i <= k and q_i + q_j <= k on each edge i+1=j: multiply the inequalities for a preimage in P_n by k, or divide the bounded vector by k to obtain a preimage. Establish signed nonnegativity before replacing q_i by the natural number z_i=q_i.toNat. At k=0 the same bounds force q=0. The scalar image really contains this zero vector, since the zero vector belongs to P_n and supplies a preimage. The sum indexed by Fin 0 is also zero; no division by zero is used. The empty path is included.

Use one palette c=0,...,k-1. At an even zero-based position i, put a one in row c exactly when c < z_i; at an odd position put a one exactly when k-z_i <= c. Each column therefore contains exactly z_i ones: Fin.card_filter_val_lt counts the initial segment, and Finset.card_filter_add_card_filter_not counts its complement. An adjacent pair has an even endpoint e and an odd endpoint o. Occupying both would require k-z_o <= c < z_e, contradicting z_e+z_o <= k. The public Adm equivalence makes each row an admissible word, and summing its zero-one occupancy entries recovers q coordinate by coordinate. In one-based coordinates the odd columns use initial segments and the even columns use final segments. Reversing row order interchanges these with the final/initial threshold convention.

Conversely, convexHull_vertices and subset_convexHull place each admissible occupancy vector in P_n. Summing its coordinate and edge bounds over exactly k rows gives the bounds above, hence the required scalar-image membership, including k=0. The hull's literature attribution supplies the convex-hull equality; the palette and scalar calculation here records its application. The scope is integer feasibility and occupancy decomposition. Comparable-support histogram uniqueness, canonical boundary uniqueness and sorting connectivity require separate arguments.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_three_pyramid`
- Truth anchor: `D5/S1/Words/AdmissibleWords/PathStableSetPolytope.convexHull_vertices`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
