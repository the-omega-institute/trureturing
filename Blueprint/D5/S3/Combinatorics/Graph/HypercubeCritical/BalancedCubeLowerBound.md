# A structural lower bound for balanced cubic cube restrictions

## Abstract

A nonempty balanced induced cubic subgraph of the actual nine-cube has at least 48 vertices.

BalancedCriticalSpectrum.IsBalanced C uses the original FALSE-prefix Huang signing from Archive.Sensitivity: sigma takes values plus or minus one on C, and M_xy = sigma(x) sigma(y) on selected ACTUAL cube edges. TRUE selects the first recursive block, so directional signs count earlier FALSE coordinates. No unproved TRUE-prefix bridge is used. Coordinate slices retain the actual Q9 vertices and unchanged matrix entries, without reidentification with Q8.

The external anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7, Problem 2, https://arxiv.org/html/2610.09483v1#Thmproblem2 : determine f₂(Q₉)=3 or 4, by selecting 258 vertices with induced maximum degree at most three or proving complete exclusion. This repository-derived structural lower bound assumes exact cubic regularity and balance; it supplies neither a 258-vertex witness nor exclusion, a Q9 solution, attainment of 48, uniqueness, classification or literature priority. The existing theorem TwoBalancedComponents.exists_two_balanced_components proves that any 258-vertex Q9 candidate of induced maximum degree at most three contains two distinct actual connected components, represented by nonempty disjoint vertex sets closed under adjacency within the candidate. Both components are balanced and cubic, each has at least 48 vertices, and their union has at least 96 vertices. This lower bound alone does not exclude a 258-vertex candidate; the external Q9 problem remains unresolved.

Precedents recorded in the companion are Laplante, Naserasr, Sunny and Wang, Sensitivity conjecture and signed hypercubes, https://hal.science/hal-04080411/document , commentary after Lemma 4.1 and Theorem 6.2, for general signed equality and switching mechanisms; Karasev, https://arxiv.org/abs/1907.11175v2 , Sections 1.2–1.3; and Mathews, https://arxiv.org/abs/1907.12357v2 , Sections 2.2–2.3, for Clifford and exterior-algebra precedents. These references are cited for the general mechanisms; no exact 48 theorem is attributed to them. Prior bounded screening did not identify this exact lower-bound statement and does not establish literature novelty. Private helpers serve the actual proof consumers and carry no independent novelty claim.

**Definition 1.1 (An actual coordinate-zero slice).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound.coordinateSlice`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound.coordinateSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For C : Finset (Q 9) and b : Bool, coordinateSlice C b is exactly C.filter (fun x => x 0 = b), still a Finset (Q 9). The two slices partition C, and the lower-bound proof chooses the smaller one. Its induced graph uses the original cube adjacency on the filtered vertices and the original Huang entries.

**Theorem 1.2 (Every nonempty balanced induced cubic restriction has at least 48 vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound.forty_eight_le_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound.forty_eight_le_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For C : Finset (Q 9), the only hypotheses are C.Nonempty, ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3, and the same original BalancedCriticalSpectrum.IsBalanced C. The conclusion is 48 ≤ C.card. Connectedness is not assumed.

Reuse BalancedCriticalSpectrum.direction_edge_count at d=3 with q = directionEdges C 0 to get 6q = |C| and q > 0 by nonemptiness. For the smaller actual coordinate-zero slice S, put N = |S| ≤ |C|/2 = 3q. Each crossing edge has one endpoint in each slice, giving exactly q degree-two vertices in S; all others have degree three. Adjacent degree-two vertices and their crossing partners would form an actual selected square, excluded by balance. Balance restricts unchanged, actual cube parity gives the bipartition, and BalancedCubeGirth gives extended girth at least eight.

Let the parity-side sizes be a,b, their degree-two counts p,r and degree-three counts h,k. Then a=p+h, b=r+k, N=a+b, q=p+r and 3(a-b)=p-r. GirthSliceCounting supplies 15h ≤ h*b+2k+4r and 15k ≤ k*a+2h+4p. Independence of degree-two vertices gives 5q ≤ 3N. With the integer d=a-b, these imply 9d² ≤ q² and 0 ≤ N²-(q+26)N+34q+2d².

The integer tail defines F = 9N²-9(q+26)N+306q+2q² ≥ 0 and uses the identity qF = (3N-5q)(21N-64q) - (7-q)(3N-q)(3N-2q). If 1 ≤ q ≤ 7, then N ≤ 3q and 5q ≤ 3N make both contributions on the right nonpositive. Since qF ≥ 0, both vanish, forcing 3N=5q and q=7, hence the impossible integer equation 3N=35. Thus q ≥ 8 and |C|=6q ≥ 48. This is an unbounded proof in integers, not a SAT or bounded enumeration certificate.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound.coordinateSlice`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound.forty_eight_le_card`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting](GirthSliceCounting.md)
