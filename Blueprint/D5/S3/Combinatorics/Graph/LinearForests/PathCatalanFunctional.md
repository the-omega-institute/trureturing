# The Catalan functional on paths

## Abstract

The integer alternating Catalan functional on actual independent sets is nonnegative on every finite path at every parameter at least its number of vertices.

**Definition 1.1 (The finite-domain functional).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional.phi`

*Formalization.* `D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any vertex type with decidable equality, any simple graph with decidable adjacency, any finite vertex domain V, and any natural parameter m, phi(G,V,m) sums (-1) to the cardinality of S times Catalan(m-card(S)) over every actual independent subset S of V. The result is an integer, and subtraction in the Catalan index is natural subtraction. Applications at m at least card(V) have every index in range. The configurations are the existing hard-core configurations using Mathlib IsIndepSet.

**Theorem 1.2 (Every legal parameter).**

$$\forall v \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; v \le m \Rightarrow 0 \le \operatorname{phi}\left(\operatorname{hasse}\left(\mathrm{Nat}\right), \operatorname{range}\left(v\right), m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional.path_phi_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural numbers v and m with v at most m, phi(hasse(Nat),range(v),m) is nonnegative. The finite domain consists of exactly the vertices 0 through v-1 of the natural-number Hasse path; adjacency means consecutive integers. This includes the empty path, m=0, and m=v.

Let F_v be the sum of (-X) to card(S) over its actual independent configurations, and let C be the Catalan generating series over the integers. The existing independent-set deletion theorem gives F_0=1, F_1=1-X and F_(v+2)=F_(v+1)-X F_v. The existing Catalan equation is X C squared plus one equals C. Induction on v gives F_(v+1) C = F_v + X^(v+2) C^(v+3). At m at least v+1, the coefficient of F_v vanishes. The remaining series is the image under natural-to-integer coefficient casting of X^(v+2) times the corresponding power of the natural Catalan series, so its coefficient is nonnegative. The empty path is the Catalan series itself. No polygon size restriction enters this argument.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional.path_phi_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional.phi`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](../../../StatisticalMechanics/HardCore/IndependentPartitionDeletion.md)
