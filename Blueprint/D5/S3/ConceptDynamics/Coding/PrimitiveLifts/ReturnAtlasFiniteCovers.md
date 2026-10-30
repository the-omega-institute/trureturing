# Finite covers of signed return atlases

## Abstract

The primitive-base period ratio is the exact degree of an intertwining map, even for infinite noncommutative deck groups.

Let A and B be complete ReturnAtlas charts over the same arbitrary group H, with positive natural periods d and e and holonomies h and k. Their full signed equality laws are A(t,z)=A(s,w) exactly when t=s+d*n and z*h^n=w for an integer n, and similarly for B. Atlas periods describe the primitive base return; they need not be the ordinary minimal periods of the lifted time maps. Every statement here concerns sets and specified deck and time maps, with no topology, finiteness, commutativity or torsion assumption on H.

**Theorem 1.1 (Unique degree and normalized seed).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), f \in \operatorname{Map}\left(X, Y\right),\; ((((\forall a \in H, x \in X,\; \operatorname{apply}\left(f, \operatorname{deck}\left(A, a, x\right)\right) = \operatorname{deck}\left(B, a, \operatorname{apply}\left(f, x\right)\right)) \land (\forall x \in X,\; \operatorname{apply}\left(f, \operatorname{time}\left(A, x\right)\right) = \operatorname{time}\left(B, \operatorname{apply}\left(f, x\right)\right)))) \implies (\exists p \in \operatorname{Prod}\left(Nat, \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), H\right)\right),\; ((((\operatorname{Positive}\left(\operatorname{first}\left(p\right)\right)) \land (((\operatorname{period}\left(A\right) = \operatorname{mul}\left(\operatorname{period}\left(B\right), \operatorname{first}\left(p\right)\right)) \land (((\operatorname{mul}\left(\operatorname{second}\left(\operatorname{second}\left(p\right)\right), \operatorname{holonomy}\left(B\right)^{\operatorname{intCast}\left(\operatorname{first}\left(p\right)\right)}\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(A\right), \operatorname{second}\left(\operatorname{second}\left(p\right)\right)\right)) \land (\forall t \in Int, z \in H,\; \operatorname{apply}\left(f, \operatorname{point}\left(A, t, z\right)\right) = \operatorname{point}\left(B, (t+\operatorname{intCast}\left(\operatorname{val}\left(\operatorname{first}\left(\operatorname{second}\left(p\right)\right)\right)\right)), \operatorname{mul}\left(z, \operatorname{second}\left(\operatorname{second}\left(p\right)\right)\right)\right)))))))) \land (\forall q \in \operatorname{Prod}\left(Nat, \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), H\right)\right),\; ((((\operatorname{Positive}\left(\operatorname{first}\left(q\right)\right)) \land (((\operatorname{period}\left(A\right) = \operatorname{mul}\left(\operatorname{period}\left(B\right), \operatorname{first}\left(q\right)\right)) \land (((\operatorname{mul}\left(\operatorname{second}\left(\operatorname{second}\left(q\right)\right), \operatorname{holonomy}\left(B\right)^{\operatorname{intCast}\left(\operatorname{first}\left(q\right)\right)}\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(A\right), \operatorname{second}\left(\operatorname{second}\left(q\right)\right)\right)) \land (\forall t \in Int, z \in H,\; \operatorname{apply}\left(f, \operatorname{point}\left(A, t, z\right)\right) = \operatorname{point}\left(B, (t+\operatorname{intCast}\left(\operatorname{val}\left(\operatorname{first}\left(\operatorname{second}\left(q\right)\right)\right)\right)), \operatorname{mul}\left(z, \operatorname{second}\left(\operatorname{second}\left(q\right)\right)\right)\right)))))))) \implies (q = p))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every f:X->Y intertwining all left deck maps and the specified time maps, there is exactly one triple (m,(r,b)) with m a positive natural, r:Fin e and b:H such that d=e*m, b*k^m=h*b, and f(A(t,z))=B(t+r.val,z*b) for all signed t and all z. The pair (r,b) is exactly the complete normalized coordinate of f(A(0,1)). The period ratio follows from the existing seam obstruction; comparing the seam again at this actual seed gives its own holonomy equation. Reducing a signed source point to complete phase coordinates and transporting holonomy powers then extends the forward law to every negative representative as well. Positivity of e makes m unique, and uniqueness of complete target coordinates makes (r,b) unique.

**Definition 1.2 (Transport with the target phase).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right),\; \forall r \in \operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), b \in H, x \in X,\; \operatorname{coveringMap}\left(A, B, r, b, x\right) = \operatorname{apply}\left(\operatorname{iterate}\left(\operatorname{time}\left(B\right), \operatorname{val}\left(r\right)\right), \operatorname{transport}\left(A, B, b, x\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.coveringMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coveringMap A B r b first applies the existing complete-coordinate transport and then advances target time by r.val. Under d=e*m and b*k^m=h*b it sends every A(t,z) to B(t+r.val,z*b), including signed t. Indeed b*k^(m*n)=h^n*b is supplied by SemiconjBy.zpow_right and zpow_mul; this is precisely what makes each source seam respected in the target, without requiring d=e.

**Theorem 1.3 (Exact existence with a prescribed seed).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), r \in \operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), b \in H,\; ((\exists f \in \operatorname{Map}\left(X, Y\right),\; ((\forall a \in H, x \in X,\; \operatorname{apply}\left(f, \operatorname{deck}\left(A, a, x\right)\right) = \operatorname{deck}\left(B, a, \operatorname{apply}\left(f, x\right)\right)) \land (((\forall x \in X,\; \operatorname{apply}\left(f, \operatorname{time}\left(A, x\right)\right) = \operatorname{time}\left(B, \operatorname{apply}\left(f, x\right)\right)) \land (\operatorname{apply}\left(f, \operatorname{point}\left(A, 0, 1\right)\right) = \operatorname{point}\left(B, \operatorname{intCast}\left(\operatorname{val}\left(r\right)\right), b\right)))))) \iff (\exists m \in Nat,\; ((\operatorname{Positive}\left(m\right)) \land (((\operatorname{period}\left(A\right) = \operatorname{mul}\left(\operatorname{period}\left(B\right), m\right)) \land (\operatorname{mul}\left(b, \operatorname{holonomy}\left(B\right)^{\operatorname{intCast}\left(m\right)}\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(A\right), b\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.map_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each prescribed r:Fin e and b:H, there exists a deck and time intertwiner f with f(A(0,1))=B(r.val,b) if and only if a positive natural m satisfies d=e*m and b*k^m=h*b. Necessity identifies the unique normalized seed in normal_form with the prescribed one. Sufficiency is the actual coveringMap A B r b on the full source carrier. Thus unequal-period maps exist exactly when the target holonomy raised to the period ratio is conjugate to the source holonomy in the displayed order.

**Definition 1.4 (The signed fiber map).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), f \in \operatorname{Map}\left(X, Y\right), m \in Nat, r \in \operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), b \in H, s \in Int, w \in H, j \in \operatorname{Fin}\left(m\right),\; ((\forall t \in Int, z \in H,\; \operatorname{apply}\left(f, \operatorname{point}\left(A, t, z\right)\right) = \operatorname{point}\left(B, (t+\operatorname{intCast}\left(\operatorname{val}\left(r\right)\right)), \operatorname{mul}\left(z, b\right)\right)) \implies (((\operatorname{apply}\left(\operatorname{fiberEnumeration}\left(A, B, f, m, r, b, s, w\right), j\right):\{x:X \mid \operatorname{apply}\left(f, x\right) = \operatorname{point}\left(B, s, w\right)\}) \land (\operatorname{val}\left(\operatorname{apply}\left(\operatorname{fiberEnumeration}\left(A, B, f, m, r, b, s, w\right), j\right)\right) = \operatorname{point}\left(A, ((s-\operatorname{intCast}\left(\operatorname{val}\left(r\right)\right))+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(B\right)\right), \operatorname{intCast}\left(\operatorname{val}\left(j\right)\right)\right)), \operatorname{mul}\left(\operatorname{mul}\left(w, \operatorname{holonomy}\left(B\right)^{(0-\operatorname{intCast}\left(\operatorname{val}\left(j\right)\right))}\right), \operatorname{inverse}\left(b\right)\right)\right)))))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.fiberEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any signed target representative B(s,w), fiberEnumeration sends j:Fin m to A(s-r.val+e*j.val,w*k^(-(j.val:Int))*b^(-1)), together with a proof that its image under f is B(s,w). This membership uses only the signed normal law: the target seam j cancels the negative power. The application suppresses the proof of that law. The degree ratio and source holonomy constraint enter when proving that this map is bijective.

**Theorem 1.5 (Signed reconstruction is injective and exhaustive).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), f \in \operatorname{Map}\left(X, Y\right), m \in Nat, r \in \operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), b \in H, s \in Int, w \in H,\; ((((\operatorname{period}\left(A\right) = \operatorname{mul}\left(\operatorname{period}\left(B\right), m\right)) \land (((\operatorname{mul}\left(b, \operatorname{holonomy}\left(B\right)^{\operatorname{intCast}\left(m\right)}\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(A\right), b\right)) \land (\forall t \in Int, z \in H,\; \operatorname{apply}\left(f, \operatorname{point}\left(A, t, z\right)\right) = \operatorname{point}\left(B, (t+\operatorname{intCast}\left(\operatorname{val}\left(r\right)\right)), \operatorname{mul}\left(z, b\right)\right)))))) \implies (\operatorname{Bijective}\left(\operatorname{fiberEnumeration}\left(A, B, f, m, r, b, s, w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.fiberEnumeration_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under d=e*m, b*k^m=h*b and the full signed normal law, the displayed fiberEnumeration is bijective for every integer s and every w:H. Injectivity uses the source seam and the Fin m bounds. Surjectivity reconstructs every source point from the residue of its target seam modulo m, using the signed power relation in its original noncommutative order. Thus every signed target representation enumerates the entire same fiber, not a chosen subfamily.

**Definition 1.6 (Every point of every fiber, exactly once).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), f \in \operatorname{Map}\left(X, Y\right), m \in Nat, r \in \operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), b \in H, y \in Y,\; ((((\operatorname{period}\left(A\right) = \operatorname{mul}\left(\operatorname{period}\left(B\right), m\right)) \land (((\operatorname{mul}\left(b, \operatorname{holonomy}\left(B\right)^{\operatorname{intCast}\left(m\right)}\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(A\right), b\right)) \land (\forall t \in Int, z \in H,\; \operatorname{apply}\left(f, \operatorname{point}\left(A, t, z\right)\right) = \operatorname{point}\left(B, (t+\operatorname{intCast}\left(\operatorname{val}\left(r\right)\right)), \operatorname{mul}\left(z, b\right)\right)))))) \implies (((\operatorname{fiberEquiv}\left(A, B, f, m, r, b, y\right):\operatorname{Equiv}\left(\operatorname{Fin}\left(m\right), \{x:X \mid \operatorname{apply}\left(f, x\right) = y\}\right)) \land (\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{val}\left(\operatorname{apply}\left(\operatorname{fiberEquiv}\left(A, B, f, m, r, b, y\right), j\right)\right) = \operatorname{point}\left(A, ((\operatorname{intCast}\left(\operatorname{val}\left(\operatorname{first}\left(\operatorname{inverseCoordinates}\left(B, y\right)\right)\right)\right)-\operatorname{intCast}\left(\operatorname{val}\left(r\right)\right))+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(B\right)\right), \operatorname{intCast}\left(\operatorname{val}\left(j\right)\right)\right)), \operatorname{mul}\left(\operatorname{mul}\left(\operatorname{second}\left(\operatorname{inverseCoordinates}\left(B, y\right)\right), \operatorname{holonomy}\left(B\right)^{(0-\operatorname{intCast}\left(\operatorname{val}\left(j\right)\right))}\right), \operatorname{inverse}\left(b\right)\right)\right)))))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.fiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given the degree, seed and signed law furnished by normal_form, fiberEquiv is an actual equivalence Fin m -> {x:X // f(x)=y} for every y:Y. Write (s,w)=B.coordinates.symm(y), where s:Fin e, so y=B(s.val,w). Its forward value at j is A(s.val-r.val+e*j.val, w*k^(-(j.val:Int))*b^(-1)). The displayed application suppresses only the proofs of the ratio, seam and signed law. The inverse is obtained from the proved bijectivity of this explicit enumeration, not from a cardinal equation. Positivity of m follows from d=e*m and positivity of the atlas periods.

The same enumeration works over any signed representative y=B(s,w): E(j)=A(s-r.val+e*j.val,w*k^(-(j.val:Int))*b^(-1)). Membership is the target seam j. If E(j)=E(l), the source return law forces j.val-l.val=m*q. The strict Fin m bounds force q=0 and j=l. Conversely, write an arbitrary preimage as A(t,z). Its image equality gives t+r.val=s+e*n and (z*b)*k^n=w for an arbitrary integer n. Euclidean division gives n=j.val+m*q even when n is negative. The source seam q and b*k^(m*q)=h^q*b then show that this original preimage is E(j). The order of w, the negative holonomy power and b inverse is essential.

The joint deck and signed time operations give a transitive H times Z action on each atlas carrier. At the normalized seed, the cyclic return stabilizer generated by the source seam maps into the target return stabilizer by multiplication of its integer parameter by m. Its index is m; the explicit enumeration realizes the corresponding m classes as a full fiber. This links arithmetic divisibility of primitive-base periods to an exact finite-fiber structure without counting the group or the ambient carriers.

For a root that routes a cycle of joint components, applying these positive degree ratios around the cycle makes their product one. Each ratio is therefore one, so each routed map has singleton fibers and is a bijection, and the component holonomies obey the degree-one conjugacy condition. This explains the equal-period transport used in the two-orbit square-root and three-orbit cube-root criteria. It is an interpretation of cyclic stabilizer inclusion and the proved fiber construction, with no claim of literature priority.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.coveringMap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.fiberEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.fiberEnumeration_bijective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.fiberEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.map_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.normal_form`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion](TwoOrbitSquareRootCriterion.md)
