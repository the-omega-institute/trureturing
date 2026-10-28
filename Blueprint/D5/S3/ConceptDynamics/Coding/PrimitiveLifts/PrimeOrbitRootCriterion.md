# Prime roots on complete return-chart families

## Abstract

Prime cardinality turns component routing into an exact local-or-cyclic root criterion.

Let p be any prime natural number, H any group, X:Fin p->Type an arbitrary dependent family, and A_i:ReturnAtlas H (X i) complete signed return charts. Write d_i>0 for their atlas periods and h_i for their holonomies. DependentReturnAtlases(H,X) denotes precisely this dependent family of charts, and Sigma(X) is the entire disjoint carrier of pairs (i,x) with x:X i. The chart equality is A_i(t,z)=A_i(s,w) exactly when t=s+d_i*m and z*h_i^m=w for some integer m. The group may be infinite and noncommutative. The d_i are primitive-base return periods, not ordinary minimal periods of the lifted time maps.

**Definition 1.1 (Time on the dependent union).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall J \in Type, X \in \operatorname{Map}\left(J, Type\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; \forall q \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(\operatorname{jointTime}\left(A\right), q\right) = \operatorname{pair}\left(\operatorname{first}\left(q\right), \operatorname{time}\left(\operatorname{apply}\left(A, \operatorname{first}\left(q\right)\right), \operatorname{second}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.jointTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary index type J and a family A_j, the time map T sends (i,x) to (i,A_i.time(x)). Every point of every chart remains in the carrier.

**Definition 1.2 (Left deck action on the dependent union).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall J \in Type, X \in \operatorname{Map}\left(J, Type\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; \forall a \in H, q \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), q\right) = \operatorname{pair}\left(\operatorname{first}\left(q\right), \operatorname{deck}\left(\operatorname{apply}\left(A, \operatorname{first}\left(q\right)\right), a, \operatorname{second}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.jointDeck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary index type J and a:H the deck map D_a sends (i,x) to (i,A_i.deck(a,x)). It uses the same left group element in each component; signed return holonomy still multiplies on the right.

**Definition 1.3 (The full signed local equation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall p \in Nat, Y \in Type, B \in \operatorname{ReturnAtlas}\left(H, Y\right),\; \operatorname{Local}\left(p, B\right) = \left(\exists s \in \operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{holonomy}\left(B\right)\right)) \land (((\operatorname{mul}\left(\operatorname{intCast}\left(p\right), \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = (1+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(B\right)\right), m\right))) \land (\operatorname{mul}\left(b^{p}, \operatorname{holonomy}\left(B\right)^{m}\right) = 1))))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.Local` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Local p B means that s:Fin B.period, m:Int and b:H satisfy b*B.holonomy=B.holonomy*b, p*s.val=1+B.period*m and b^p*B.holonomy^m=1. The integer m can be negative. This is the existing exact ReturnAtlas.root_criterion equation, with no ordinary-time-period replacement.

**Theorem 1.4 (Exact prime-family root criterion).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall p \in Nat, X \in \operatorname{Map}\left(\operatorname{Fin}\left(p\right), Type\right), A \in \operatorname{DependentReturnAtlases}\left(H, X\right),\; \operatorname{Prime}\left(p\right) \implies ((\exists R \in \operatorname{Map}\left(\operatorname{Sigma}\left(X\right), \operatorname{Sigma}\left(X\right)\right),\; ((\forall a \in H, q \in \operatorname{Sigma}\left(X\right),\; \operatorname{apply}\left(R, \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), q\right)\right) = \operatorname{apply}\left(\operatorname{jointDeck}\left(A, a\right), \operatorname{apply}\left(R, q\right)\right)) \land (\operatorname{iterate}\left(R, p\right) = \operatorname{jointTime}\left(A\right)))) \iff (((\forall i \in \operatorname{Fin}\left(p\right),\; \exists s \in \operatorname{Fin}\left(\operatorname{period}\left(\operatorname{apply}\left(A, i\right)\right)\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{holonomy}\left(\operatorname{apply}\left(A, i\right)\right)\right)) \land (((\operatorname{mul}\left(\operatorname{intCast}\left(p\right), \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = (1+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(\operatorname{apply}\left(A, i\right)\right)\right), m\right))) \land (\operatorname{mul}\left(b^{p}, \operatorname{holonomy}\left(\operatorname{apply}\left(A, i\right)\right)^{m}\right) = 1))))) \lor (\forall i \in \operatorname{Fin}\left(p\right), j \in \operatorname{Fin}\left(p\right),\; ((\operatorname{period}\left(\operatorname{apply}\left(A, i\right)\right) = \operatorname{period}\left(\operatorname{apply}\left(A, j\right)\right)) \land (\exists b \in H,\; \operatorname{mul}\left(b, \operatorname{holonomy}\left(\operatorname{apply}\left(A, j\right)\right)\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(\operatorname{apply}\left(A, i\right)\right), b\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.prime_root_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists a map R:Sigma X->Sigma X with R(D_a(q))=D_a(R(q)) for every a and q, and R iterated p times equal to T, if and only if either every A_i satisfies Local p A_i or for every i,j one has d_i=d_j and some b:H with b*h_j=h_i*b. The two alternatives may overlap. R is not assumed to preserve charts, be bijective, or commute with time.

Necessity first derives time commutation from R^p=T and injectivity from the injectivity of T. Completeness of each chart makes the target component of R(i,x) independent of x: deck moves cover its group coordinate, and nonnegative time moves cover its normalized finite phase. This induces sigma:Fin p->Fin p with sigma^p=id. Each restricted map between routed components is injective and intertwines deck and time. Apply ReturnAtlasFiniteCovers.normal_form and its actual fiberEquiv: a positive degree m gives Fin m equivalent to the full preimage of every target point. Injectivity forces any two such preimages equal; if m>1 the images of 0 and 1 contradict injectivity of that equivalence. Hence m=1, yielding equal atlas periods and b*h_j=h_i*b without counting H.

If sigma fixes every index, restriction gives an actual pth root in each chart, and the existing local root criterion gives all local equations. Otherwise choose a nonfixed index o. Mathlib's prime minimal-period theorem gives minimalPeriod(sigma,o)=p. Its p distinct iterates exhaust Fin p. Apply the same injective-factor argument to every iterate of R to identify A_o with every chart. Inverting and composing the resulting conjugacies gives the displayed condition for every ordered pair i,j. No fixed-order enumeration is used.

For sufficiency, local roots combine directly on the dependent union. In the other case choose gauges b_i with b_i*h_i=h_o*b_i and equal periods. Existing complete-coordinate transport identifies the entire union with Fin p times X_o, by (i,x)->(i,transport(A_i,A_o,b_i inverse,x)). In these coordinates define C(i,y)=((i.val+1) mod p, T_o^floor((i.val+1)/p)(y)). Induction proves C^n(i,y)=((i.val+n) mod p, T_o^floor((i.val+n)/p)(y)). Thus C^p(i,y)=(i,T_o(y)); exactly one time step occurs at the wrap. Deck commutation of T_o makes C deck equivariant. Conjugating C back through the full chart equivalence constructs the required actual map R.

This connects cyclic permutation arithmetic, the signed finite-cover degree, and nonabelian holonomy conjugacy. The restriction to exactly p charts makes a single nonfixed prime orbit fill the entire index set. Larger finite families require additional orbit multiplicity information; no criterion for those families is asserted here. These arguments combine established permutation and return-chart mechanisms, with no claim of literature priority.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.Local`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.jointDeck`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.jointTime`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.prime_root_criterion`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers](ReturnAtlasFiniteCovers.md)
