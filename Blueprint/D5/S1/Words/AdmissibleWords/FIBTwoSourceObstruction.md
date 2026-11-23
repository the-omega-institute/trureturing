# A joint bound from two sources

## Abstract

Two oriented differences compete for the same region of a containing event.

**Theorem 1.1 (Two disjoint differences under a shared capacity).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.shared_capacity`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.shared_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S and W be contained in both H and K, and let T be contained in K. With K of finite measure and S, H and T measurable, the sum of the masses of W outside S and T outside H is at most the mass of K minus the mass of S. The first difference lies in H and the second avoids H. Both lie in K outside S.

**Theorem 1.2 (Exact joint range of the two differences).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.five_vertex_range`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.five_vertex_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real q and c, prescribe Lebesgue mass q at S, T and W, and mass q plus c at H and K. All five events are measurable subsets of the half-open unit interval. Impose the inclusions of the shared capacity bound. A pair of difference masses a for W outside S and b for T outside H is realizable exactly when both are nonnegative and at most q, their sum is at most c, and b is at most the mass outside H. For attainment, reserve the last interval of length b in K for T outside H and replace it in H by an interval of the same length outside K. This leaves the interval needed by W outside S within both H and K. The inequalities imply that both q and c are nonnegative and q plus c is at most one.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.five_vertex_range`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.shared_capacity`
