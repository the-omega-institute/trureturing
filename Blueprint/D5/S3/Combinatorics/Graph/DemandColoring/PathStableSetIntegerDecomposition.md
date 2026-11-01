# Integer decomposition of the path stable-set polytope

## Abstract

Signed lattice points in natural dilates of the path stable-set polytope are sums of admissible occupancy vectors.

**Theorem 1.1 (Exact natural path demands).**

Lean statement: `D5/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition.exists_admissible_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition.exists_admissible_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural n and k and z from Fin n to the natural numbers, assume z(i)<=k for every coordinate and z(i)+z(j)<=k whenever i.val+1=j.val. There exists W from Fin k to Fin n to Bool with AdmissibleCount.Adm n (W c) for every c, and exactly z(i) indices c satisfying W(c,i)=true for each i. Apply the same two-color allocation to Mathlib's native pathGraph.bicoloring. The existing no-adjacent-true equivalence supplies the original recursive Adm.

**Theorem 1.2 (Signed lattice points in the actual scalar image).**

Lean statement: `D5/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition.lattice_mem_nat_smul_polytope_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition.lattice_mem_nat_smul_polytope_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and k and every q from Fin n to the integers, put q_real(i)=(q(i):Real). Then q_real belongs to (k:Real) times the existing PathStableSetPolytope.polytope n if and only if there exists W from Fin k to Fin n to Bool such that every W c satisfies the existing recursive AdmissibleCount.Adm n and q_real equals the vector sum over c of the existing PathStableSetPolytope.occupancy (W c). This is exactly k indexed summands; empty or repeated words are allowed. The carrier, occupancy and admissibility predicate are unchanged.

Multiplying the original polytope inequalities by k gives nonnegative signed integer coordinates bounded by k and edge sums bounded by k. Only after nonnegativity is established are the coordinates converted to natural demands. Exact palette counts give the required vector sum. Conversely each admissible occupancy lies in the polytope by its existing convex-hull theorem. Summing coordinate and edge inequalities gives the scaled bounds. For positive k, division by k supplies an actual preimage in the original polytope. For k=0 the vector is zero and the zero vector in that nonempty polytope is an explicit scalar-image preimage. The empty path, singleton interval, negative integer coordinates, saturated demands and tight edges are all included.

This is the integer decomposition property of the path stable-set polytope, proved by classical bipartite interval allocation. It establishes feasibility; no uniqueness of a comparable threshold-chain histogram is asserted. The broader chain-polytope and perfect-graph context is classical.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition.exists_admissible_layers`
- Truth anchor: `D5/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition.lattice_mem_nat_smul_polytope_iff`
- Dependency: [D5/S1/Words/AdmissibleWords/PathStableSetPolytope](../../../../S1/Words/AdmissibleWords/PathStableSetPolytope.md)
- Dependency: [D5/S3/Combinatorics/Graph/DemandColoring/BipartiteDemandColoring](BipartiteDemandColoring.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
