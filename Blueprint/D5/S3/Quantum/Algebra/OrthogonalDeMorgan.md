# Orthogonal De Morgan Identities

## Abstract

Orthogonal complementation exchanges joins and meets of closed subspaces.

**Theorem 1.1 (Orthogonal complements exchange joins and meets).**

$$\forall k, E: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}_{k}(E)],\ [\operatorname{CompleteSpace}(E)],\ M, N: \operatorname{ClosedSubmodule}_{k}(E),\ \operatorname{orthogonal}\left(\operatorname{join}\left(M, N\right)\right) = \operatorname{meet}\left(\operatorname{orthogonal}\left(M\right), \operatorname{orthogonal}\left(N\right)\right) \land \operatorname{orthogonal}\left(\operatorname{meet}\left(M, N\right)\right) = \operatorname{join}\left(\operatorname{orthogonal}\left(M\right), \operatorname{orthogonal}\left(N\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OrthogonalDeMorgan.orthogonal_de_morgan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a real-or-complex scalar field, E a complete inner-product space over k, and M and N closed subspaces. Orthogonal complementation sends the closed join of M and N to the meet of their orthogonal complements, and sends their meet to the closed join of their orthogonal complements.

The join operation on ClosedSubmodule is the closure of the algebraic sum. Thus the second equality is exactly the source statement that the orthogonal complement of an intersection is the closure of the sum of the two orthogonal complements.

Repository search found no D5 declaration of this pair of identities. The pinned Mathlib tree contains the exact declarations ClosedSubmodule.inf_orthogonal and ClosedSubmodule.sup_orthogonal, which are imported and applied directly. The ordered search stopped at this exact Mathlib hit, before third-party libraries.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OrthogonalDeMorgan.orthogonal_de_morgan`
