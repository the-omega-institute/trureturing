# Finite families and exact root multiplicities

## Abstract

Allowed component cycles give an exact additive criterion for equivariant roots on any finite chart family.

Let H be any group, iota any finite type, X:iota->Type any dependent family, and A_i:ReturnAtlas H (X i) complete signed return charts. No finiteness or commutativity is required of H. The finite index type may be empty. Write d_i>0 for the atlas period and h_i for the holonomy. Each chart covers its entire carrier and satisfies A_i(t,z)=A_i(s,w) exactly when t=s+d_i*m and z*h_i^m=w for some integer m. These periods describe the primitive base returns, rather than the ordinary periods of the lifted time maps.

On Sigma X, T(i,x)=(i,A_i.time(x)) and D_a(i,x)=(i,A_i.deck(a,x)) are the existing jointTime and jointDeck. Isotypic A i j means d_i=d_j and there exists b:H with b*h_j=h_i*b. It is an equivalence relation, expressing equal periods and conjugate holonomy. IsotypicClass(A,i) denotes the subtype {j:iota | Isotypic A i j}, and NatCard is its finite cardinality. Local q B is the existing signed local equation: there exist s:Fin B.period, m:Int and b:H with b commuting with B.holonomy, q*s.val=1+B.period*m, and b^q*B.holonomy^m=1. The integer m is unrestricted in sign.

**Theorem 1.1 (Exact additive multiplicity criterion).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall iota \in Type, X \in \operatorname{Map}\left(iota, Type\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; [\operatorname{Finite}\left(iota\right)]\forall k \in Nat,\; 0 < k \implies ((\exists R \in \operatorname{Map}\left(\operatorname{Sigma}\left(X\right), \operatorname{Sigma}\left(X\right)\right),\; ((\forall a \in H, x \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(R, \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), x\right)\right) = \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), \operatorname{apply}\left(R, x\right)\right)) \land (\operatorname{iterate}\left(R, k\right) = \operatorname{jointTime}\left(A\right)))) \iff (\forall i \in iota,\; \exists L \in \operatorname{List}\left(Nat\right),\; ((\operatorname{sum}\left(L\right) = \operatorname{NatCard}\left(\operatorname{IsotypicClass}\left(A, i\right)\right)) \land (\forall ell \in Nat,\; \operatorname{Mem}\left(ell, L\right) \implies ((0 < ell) \land (((\operatorname{Divides}\left(ell, k\right)) \land (\operatorname{Local}\left(\operatorname{natDiv}\left(k, ell\right), \operatorname{apply}\left(A, i\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion.finite_root_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural k, an unrestricted map R:Sigma X->Sigma X with R(D_a(x))=D_a(R(x)) for all a,x and R iterated k times equal to T exists if and only if, for every index i, there is an actual finite list L of natural block lengths whose sum is the cardinality of {j | Isotypic A i j}, and each ell in L is positive, divides k, and satisfies Local (k/ell) A_i. Repeated lengths are permitted. The statement assumes neither bijectivity, time commutation nor component preservation of R.

Necessity begins with R^k=T. Since T is injective and k is positive, R is injective; R also commutes with T. Completeness of each chart and deck equivariance make the output component constant on that whole chart. Thus R induces a component permutation sigma with sigma^k=id. The existing routing_isotypic proof uses ReturnAtlasFiniteCovers.normal_form and the full fiberEquiv: an injective factor cannot have positive covering degree greater than one, even when H is infinite. Hence every component is isotypic to its image under sigma.

Fix i and restrict sigma to the finite class {j | Isotypic A i j}. The SameCycle quotient includes both moving cycles and fixed points. For a cycle representative j its length ell is minimalPeriod(sigma,j), which is positive and divides k. The existing iterate-distinctness and iterate-mod-period identities identify the entire cycle with Fin ell, so its actual cardinality is ell. Fintype's sigma-fiber equivalence then makes the class cardinality the sum of these lengths.

Because sigma^ell fixes j, the actual map R^ell restricts to X_j. Its (k/ell)-fold iterate is T_j, and it remains deck equivariant. Apply ReturnAtlas.root_criterion to obtain Local (k/ell) A_j. Equal atlas periods and holonomy conjugacy give a chart equivalence intertwining deck and time, so the local root transfers to A_i. These are the required allowed lengths for the fixed class.

For sufficiency, quotient iota by Isotypic and choose one representative in each class. Its length list L gives a finite type of positions (t,j) with t:Fin L.length and j:Fin L[t]. Its cardinality is L.sum, so a finite equivalence partitions the actual class into precisely those blocks. The construction chooses no index in an empty class; when iota is empty, both the quotient and the constructed carrier are empty.

Choose a local q-root f on the representative chart of each block, where q=k/ell. Gauges built from the existing complete coordinates and right multiplication identify every chart in that block with the representative chart. On Fin ell times that carrier define C(j,y)=((j.val+1) mod ell, f^floor((j.val+1)/ell)(y)). The reused cycleStep_iterate identity gives C^n(j,y)=((j.val+n) mod ell, f^floor((j.val+n)/ell)(y)). Since ell divides k, at n=k the first coordinate returns to j and the second becomes f^(k/ell)(y)=T(y). Deck equivariance of f makes every carry deck equivariant. Combine the block maps and conjugate through the full dependent chart equivalence to obtain R on Sigma X.

The numerical condition is membership in the additive monoid generated by the allowed positive divisors of k. A greatest-common-divisor divisibility condition alone need not express this membership: for example, sums of 2 and 3 include every natural number at least 2 and exclude 1, although their greatest common divisor is 1. The theorem keeps the actual list of lengths. It extends the earlier two-chart, three-chart and prime-cardinality mechanisms by retaining all component-cycle multiplicities. No literature priority is claimed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion.finite_root_criterion`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion](PrimeOrbitRootCriterion.md)
