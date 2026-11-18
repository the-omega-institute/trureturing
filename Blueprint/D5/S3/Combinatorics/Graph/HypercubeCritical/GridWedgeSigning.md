# Actual Huang balance of the grid-wedge support

## Abstract

The literal TRUE-row grid-wedge support has an explicit switching for the actual FALSE-prefix Huang matrix in every square dimension d*d with d at least two.

The external motivation is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2: https://arxiv.org/html/2610.09483v1#Thmproblem2 . The question asks whether f₂(Q₉)=3 or 4. GridWedgeSupport already establishes the literal support's cardinality 4*(d-1)*d^(d-1) and induced regular degree d. GridWedgeComponent constructs its TRUE-prefix integer signing. The result here supplies the missing executable conversion to Huang's fixed FALSE-prefix matrix. The general equality and switching mechanisms discussed in GridWedgeComponent are prior work; no literature novelty or priority is claimed.

**Definition 1.1 (The same literal support as a finite set).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.supportFinset`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.supportFinset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every d : Nat and hd : 2 ≤ d, supportFinset hd is Finset.univ.filter (fun x => x ∈ GridWedgeComponent.support hd), with x a literal Boolean function on Fin(d*d). Membership is exactly the existing upper, lower-double or lower-transversal row pattern, with no added geometric or balance assumption.

**Definition 1.2 (An explicit potential times the existing TRUE-prefix switching).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.switching`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.switching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every d : Nat, hd : 2 ≤ d and x : Fin(d*d) → Bool, switching hd x is theta(x) times the real cast of the existing integer switchSign hd x. Here theta(x) is the product, over all coordinate indices k, of (-1)^k.val when x(k) is TRUE and 1 otherwise. The reused switchSign is (-1)^e: e is the sum of rowPrefix(x,r) over empty rows r, plus 1 exactly for a lower transversal containing the marked coordinate in row zero. These are constructed values on actual Boolean vertices, not a hypothesized gauge or signing.

**Theorem 1.3 (Every support edge obeys the original Huang coefficient law).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.support_isSwitching`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.support_isSwitching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d : Nat and hd : 2 ≤ d, BalancedCriticalSpectrum.IsSwitching (supportFinset hd) (switching hd). Thus each selected switching value is 1 or -1, and for all selected x,y joined by actual hypercube adjacency, huangMatrix (d*d) x y = switching hd x * switching hd y. There are no signing, cycle-product, balance, eigenvector or wedge-coefficient hypotheses.

The potential satisfies theta(x)*theta(flip(x,k))=(-1)^k.val: all unchanged coordinate factors square to one. The literal row-major order is proved to agree with lexicographic row and column order. Consequently the product of TRUE-prefix factors equals the real cast of gridEdgeSign. The existing GrayGridComponent.matrix_flip_prefix gives the actual FALSE-prefix Huang coefficient. At each earlier coordinate, its FALSE factor is minus the TRUE factor; their product is (-1)^k.val. This proves the exact convention conversion.

The consumed GridWedgeComponent.sign_lower_edge handles every lower-double and transversal flip. At a lower-double vertex only the empty row can be filled, and its TRUE-prefix sign is (-1) to the rowPrefix of that missing row. For a transversal, the two marked-row cases give respectively -1 and +1 on all legal additions. The existing upper/lower weight laws force every upper edge to meet a lower vertex, so reversing the flip covers it as well. Multiplication by theta now gives the actual Huang law on all support edges, including d=2.

General actual balance is the new conclusion. Source cardinality and regularity are reused, not reproved as new results. At d=3 the known cardinality is 72. This theorem supplies its actual balanced component but does not formalize a thin-slice threshold of 19, a universal 54-point classification, the E15 boundary, or the full 258-point obstruction. The original Hong–Wu–Xia problem remains unresolved.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.supportFinset`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.support_isSwitching`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning.switching`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GrayGridComponent](GrayGridComponent.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent](GridWedgeComponent.md)
