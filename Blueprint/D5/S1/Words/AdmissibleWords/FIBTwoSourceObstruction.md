# A joint bound from two sources

## Abstract

Two oriented differences compete for the same region of a containing event.

**Theorem 1.1 (Two disjoint differences under a shared capacity).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.shared_capacity`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.shared_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S and W be contained in both H and K, and let T be contained in K. Under a finite measure with S, H and T measurable, the sum of the masses of W outside S and T outside H is at most the mass of K minus the mass of S. The first difference lies in H and the second avoids H. Both lie in K outside S.

**Theorem 1.2 (Individually sharp differences on five vertices).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.five_vertex_obstruction`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.five_vertex_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set the marginal masses of S, H, K, T and W to three, four, four, three and three sixths. The inclusion relations are those of the shared capacity bound. One six-outcome uniform law gives W outside S mass one sixth and T outside H mass zero. A second gives the reverse pair of masses. Under any finite measure with the same marginal masses and measurable events, their sum is at most one sixth. Each individual maximum is therefore one sixth.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.five_vertex_obstruction`
- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBTwoSourceObstruction.shared_capacity`
