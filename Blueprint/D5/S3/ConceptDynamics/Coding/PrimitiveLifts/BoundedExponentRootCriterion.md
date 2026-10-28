# Universal roots over groups of bounded exponent

## Abstract

For a group of bounded exponent, roots of every positive degree exist precisely when every finite actual isotypic class has trivial return data.

Let u, v and w be independent universes. Let H:Type u be any group satisfying Mathlib's Monoid.ExponentExists H: there is a positive natural E with b^E=1 for every b:H. This assumption allows infinite and noncommutative groups. Let iota:Type w be arbitrary, X:iota->Type v a dependent family, and A_i:ReturnAtlas H (X i) complete signed return atlases. The family may be empty and may contain both finite and infinite actual isotypic classes.

Write d_i=(A_i).period>0 and h_i=(A_i).holonomy. The complete chart covers X i by A_i.point(t,z), for t:Int and z:H, with equality exactly when t=s+d_i*m and z*h_i^m=w for an integer m. Its time adds one to t and its left deck action multiplies z on the left. On Sigma X, T=jointTime A and D_a=jointDeck A a act by these maps within each component. Isotypic A i j means equal periods and holonomy conjugacy: d_i=d_j and some b:H satisfies b*h_j=h_i*b. IsotypicClass(A,i) is the actual subtype {j:iota | Isotypic A i j}. ExponentExists and TypeAt in the formula denote the Mathlib predicate and the indicated universe, respectively.

**Theorem 1.1 (Exact arbitrary-family criterion).**

$$\forall u \in Universe, v \in Universe, w \in Universe,\; \forall H \in \operatorname{TypeAt}\left(u\right),\; [\operatorname{Group}\left(H\right)]\operatorname{ExponentExists}\left(H\right) \implies \forall iota \in \operatorname{TypeAt}\left(w\right), X \in \operatorname{Map}\left(iota, \operatorname{TypeAt}\left(v\right)\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; (\forall k \in Nat,\; 0 < k \implies \exists R \in \operatorname{Map}\left(\operatorname{Sigma}\left(X\right), \operatorname{Sigma}\left(X\right)\right),\; ((\forall a \in H, q \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(R, \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), q\right)\right) = \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), \operatorname{apply}\left(R, q\right)\right)) \land (\operatorname{iterate}\left(R, k\right) = \operatorname{jointTime}\left(A\right)))) \iff (\forall i \in iota,\; \operatorname{Finite}\left(\operatorname{IsotypicClass}\left(A, i\right)\right) \implies ((\operatorname{period}\left(\operatorname{apply}\left(A, i\right)\right) = 1) \land (\operatorname{holonomy}\left(\operatorname{apply}\left(A, i\right)\right) = 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/BoundedExponentRootCriterion.universal_rootability_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural k there exists an actual map R:Sigma X->Sigma X commuting with every left deck map and satisfying R iterated k times equal to T if and only if every finite actual isotypic class has period one and holonomy one. R may route between components. Neither component preservation nor bijectivity is assumed. The existential choice of R is inside the quantifier over k; no compatibility, commutation or coherent choice between different degrees is required.

The proof uses FiniteOrbitRootCriterion.arbitrary_root_criterion exactly on this entire dependent carrier. For a fixed positive degree k, that criterion characterizes a root by a list L of positive block lengths for each i, summing to Nat.card C_i, where C_i is the actual isotypic class. Every ell in L divides k and satisfies Local (k/ell) A_i. Here Local q A_i means that there exist s:Fin d_i, m:Int and b:H with Commute b h_i, q*s.val=1+d_i*m, and b^q*h_i^m=1.

For necessity, fix a finite C_i. It contains i by reflexivity of Isotypic, so N=Nat.card C_i is positive. Choose the single test degree k=N!*d_i*E, using the positive Mathlib exponent E=Monoid.exponent H. The resulting list has positive sum N and therefore has an entry ell. Since all entries are nonnegative, ell<=N, so Nat.dvd_factorial gives ell dividing N!. Consequently both d_i and E divide q=k/ell. This bound accounts for every possible routing cycle in that finite class; it makes no assertion about routing in an infinite class.

The local phase equation q*s.val=1+d_i*m now forces d_i to divide one. Positivity gives d_i=1. The sole value of Fin 1 is zero, and the same integer equation gives m=-1. Since E divides q, the common exponent law gives b^q=1. The holonomy equation reduces to h_i inverse=1, hence h_i=1. The argument uses no commutation among different group elements and needs no nilpotence or finite cardinality of H.

For sufficiency, fix k>0. In a finite C_i use a list of N copies of one. Its sum is N, and each entry has the required local equation with d_i=1, h_i=1, s=0, m=-1 and b=1. In an infinite C_i use the empty list: Mathlib's Nat.card C_i=0 convention makes the sum condition true and the entry conditions vacuous. This does not replace the infinite class by an empty carrier. The arbitrary-index criterion constructs its roots by an actual equivalence C_i equivalent to C_i times Fin k, partitioning the infinite multiplicity into full k-blocks. It assembles those blocks with all finite classes to give a root on the full Sigma X. For an empty index type both sides hold and the constructed map is the unique map on the empty carrier.

As mathematical context, a positive common exponent also forces every group homomorphism from the additive rationals to H to be trivial: for a rational r write r=E*(r/E), then the homomorphism identity and the exponent law give the image of r equal to one. This concerns coherent rational homomorphisms. The theorem above concerns separate roots at each degree and asserts no classification of rational flows. The result is derived from the existing root criterion and bounded-exponent arithmetic; no novelty or priority claim is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/BoundedExponentRootCriterion.universal_rootability_iff`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion](FiniteOrbitRootCriterion.md)
