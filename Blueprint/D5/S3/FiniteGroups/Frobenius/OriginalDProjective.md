# Original-D Frobenius projectivity

## Abstract

Projectivity of the actual original-D Frobenius module by coordinate sections and relative trace.

**Theorem 1.1 (Projectivity from the kernel order).**

$$\forall k \in Type*,\; \forall G \in Type*,\; \forall V \in Type*,\; [Group\left(G\right)], [Finite\left(G\right)], [Field\left(k\right)], [AddCommGroup\left(V\right)], [Module\left(k, V\right)], \forall N \in Subgroup\left(G\right),\; [\operatorname{Subgroup}.\operatorname{Normal}\left(N\right)], \forall rho \in Representation\left(k, G, V\right),\; [\operatorname{Module}.\operatorname{Finite}\left(k, V\right)], [\operatorname{Representation}.\operatorname{IsIrreducible}\left(rho\right)], \forall hfix \in \left(\forall g \in G,\; \neg (\operatorname{Membership}.\operatorname{mem}\left(N, g\right)) \Rightarrow \left(\forall n \in N,\; \operatorname{MulAut}.\operatorname{conjNormal}\left(g\right)\left(n\right) = n \Rightarrow n = 1\right)\right),\; \forall hnt \in \neg (\operatorname{Representation}.\operatorname{IsTrivial}\left(\operatorname{MonoidHom}.\operatorname{comp}\left(rho, \operatorname{Subgroup}.\operatorname{subtype}\left(N\right)\right)\right)),\; \forall hunit \in IsUnit\left((\operatorname{Nat}.\operatorname{card}\left(N\right) : k)\right),\; \operatorname{Module}.\operatorname{Projective}\left(MonoidAlgebra\left(k, G\right), \operatorname{Representation}.\operatorname{asModule}\left(rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Frobenius/OriginalDProjective.projective_originalD` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any field, G a finite group, N a normal subgroup, and rho a finite-dimensional irreducible representation whose restriction to N is nontrivial. Suppose every conjugation by an element outside N fixes only the identity in N. If the image of |N| in k is a unit, then W = rho.asModule is projective over the actual group algebra k[G]. The field, group and carrier universes are independent.

Use exists_complement_originalD_regular to obtain the actual complement C, the D-submodule S of W and the equivariant coordinates E : W -> (C -> S), where D is literally Module.End k[G] W. Existing scalar-tower instances restrict E to the original field k. For a surjection f : P -> W, choose a k-linear section t and put j(z) = E^(-1)(delta_1(z)). Define s_C(v) = sum over c in C of c t(j(E(v)(c))). The coordinate law gives E(c j(z)) = delta_c(z), so f(s_C(v)) = v by coordinate reconstruction. Reindexing c by d^(-1)c proves s_C(d v) = d s_C(v). This constructs a section from regular coordinates without dividing by |C|.

For g in G set A_g(v) = g s_C(g^(-1)v). Complement equivariance proves A_(gc) = A_g, so the summand descends to the left-coset set G/C even when C is not normal. Sum the descended k-linear maps over this finite quotient. Left multiplication permutes G/C and proves that the sum T commutes with every G operator. The existing equivariantOfLinearOfComm interface makes T a k[G]-linear map. Every coset contributes v to f(T(v)), hence f(T(v)) = [G:C] v. The complement identity gives [G:C] = |N|. Multiplying T by the inverse of this scalar splits f. Applying this construction to the canonical free surjection proves projectivity without a Small assumption.

The characteristic boundary comes entirely from the last normalization: only |N| must be invertible in k. The proof imposes no invertibility condition on |C| or |G|, no normality of C, no commutativity of D and no new scalar-tower hypothesis. It asserts no converse in other characteristics. This formal integration uses the existing original-D regular-coordinate theorem, vector-space projectivity and the classical relative-trace argument; it makes no novelty claim and includes no separately formalized finite-field example.

## References

- Truth anchor: `D5/S3/FiniteGroups/Frobenius/OriginalDProjective.projective_originalD`
- Dependency: [D5/S3/FiniteGroups/Frobenius/OriginalDFrobenius](OriginalDFrobenius.md)
