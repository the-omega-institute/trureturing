# Universal independent roots over arbitrary groups

## Abstract

For an arbitrary group, roots of every positive degree exist precisely when every finite actual isotypic class has period one and infinitely divisible holonomy.

Let u, v and w be independent universes. Let H:Type u be any group, with no finiteness, exponent, commutativity or nilpotence assumption. Let iota:Type w be arbitrary, X:iota->Type v a dependent family, and A_i:ReturnAtlas H (X i) complete signed return atlases. The family may be empty and may contain both finite and infinite actual isotypic classes.

Write d_i=(A_i).period>0 and h_i=(A_i).holonomy. The complete chart covers X i by A_i.point(t,z), for t:Int and z:H, with equality exactly when t=s+d_i*m and z*h_i^m=w for an integer m. Its time adds one to t and its left deck action multiplies z on the left. On Sigma X, T=jointTime A and D_a=jointDeck A a act by these maps within each component. Isotypic A i j means equal periods and holonomy conjugacy: d_i=d_j and some b:H satisfies b*h_j=h_i*b. IsotypicClass(A,i) is the actual subtype {j:iota | Isotypic A i j}.

**Theorem 1.1 (Exact arbitrary-family criterion).**

$$\forall u \in Universe, v \in Universe, w \in Universe, H \in \operatorname{TypeAt}\left(u\right),\; [\operatorname{Group}\left(H\right)]\forall iota \in \operatorname{TypeAt}\left(w\right), X \in \operatorname{Map}\left(iota, \operatorname{TypeAt}\left(v\right)\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; (\forall k \in Nat,\; 0 < k \implies \exists R \in \operatorname{Map}\left(\operatorname{Sigma}\left(X\right), \operatorname{Sigma}\left(X\right)\right),\; ((\forall a \in H, q \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(R, \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), q\right)\right) = \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), \operatorname{apply}\left(R, q\right)\right)) \land (\operatorname{iterate}\left(R, k\right) = \operatorname{jointTime}\left(A\right)))) \iff (\forall i \in iota,\; \operatorname{Finite}\left(\operatorname{IsotypicClass}\left(A, i\right)\right) \implies ((\operatorname{period}\left(\operatorname{apply}\left(A, i\right)\right) = 1) \land (\forall n \in Nat,\; 0 < n \implies \exists b \in H,\; \operatorname{pow}\left(b, n\right) = \operatorname{holonomy}\left(\operatorname{apply}\left(A, i\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/UniversalRootCriterion.universal_rootability_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural k there exists an actual map R:Sigma X->Sigma X commuting with every left deck map and satisfying R iterated k times equal to T if and only if every finite actual isotypic class has period one and its holonomy has an n-th root in H for every positive n. R may route between components. Neither component preservation nor bijectivity is assumed. The existential choice of R is inside the quantifier over k; no compatibility, commutation or coherent choice between different degrees is required.

The proof applies FiniteOrbitRootCriterion.arbitrary_root_criterion exactly on this entire dependent carrier. For a fixed positive degree k, that criterion characterizes a root by a list L of positive block lengths for each i, summing to Nat.card C_i, where C_i is the actual isotypic class. Every ell in L divides k and satisfies Local (k/ell) A_i. Here Local q A_i means that there exist s:Fin d_i, m:Int and b:H with Commute b h_i, q*s.val=1+d_i*m, and b^q*h_i^m=1.

For necessity, fix a finite C_i and put N=Nat.card C_i>0. For each positive n, test k=N!*d_i*n. The resulting list has positive sum N and therefore has an entry ell. Since every entry is positive and sums to N, ell<=N, so Nat.dvd_factorial gives ell dividing N!. Thus q=k/ell is divisible by both d_i and n. The local phase equation q*s.val=1+d_i*m then forces d_i to divide one, hence d_i=1; the sole value of Fin 1 gives s=0 and the same equation gives m=-1. The holonomy equation becomes b^q*h_i^-1=1, so b^q=h_i. Writing q=n*r extracts (b^r)^n=h_i. Taking n=1 supplies the period clause, while each positive n supplies its own root.

For sufficiency, fix k>0. In a finite C_i use a list of N copies of one. Choose an element b with b^k=h_i. Since h_i=b^k, b commutes with h_i by Commute.self_pow; with d_i=1, s=0 and m=-1 this is exactly Local k A_i. In an infinite C_i use the empty list: the arbitrary-index criterion partitions the actual infinite isotypic fiber into full k-blocks, so no multiplicity condition is imposed. The construction retains those infinite classes as genuine carriers. The criterion then assembles the blocks into a global deck-equivariant root.

Independent roots are chosen separately for each degree; no coherent rational action is asserted. The theorem is an arbitrary-group statement and makes no novelty or priority claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/UniversalRootCriterion.universal_rootability_iff`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion](FiniteOrbitRootCriterion.md)
