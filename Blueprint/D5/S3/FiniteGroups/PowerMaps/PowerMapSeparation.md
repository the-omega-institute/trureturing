# Separate power maps and a joint obstruction

## Abstract

Two groups of order 4374 have separately conjugate integer-power maps but no common square-cube conjugacy.

**Definition 1.1 (The field of three elements).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.F`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F is ZMod 3. All seven non-Boolean coordinates and every bilinear expression below are evaluated in this field.

**Definition 1.2 (The two original-coordinate carriers).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.S`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean i, S(i) has coordinates (a,b,x,y,z,s,t,e), with the first seven in F and e Boolean. Write v=(a,b), w=(x,y,z) and c=(s,t). False selects the first group G and true the second group H. These are the original, uncentered coordinates, including the free third coordinate z of w in H.

**Definition 1.3 (The finite Cartesian parametrization).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.productEquiv`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.productEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each Boolean i, productEquiv(i) maps (a,b,x,y,z,s,t,e) to ((a,b),(x,y,z),(s,t),e), an equivalence with F squared times F cubed times F squared times Bool. Its inverse unpacks the coordinates. The induced finite structure has cardinality 3 squared times 3 cubed times 3 squared times 2, namely 4374.

**Definition 1.4 (The involution sign).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.sign`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.sign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean e, sign(e) is minus one if e is true and one otherwise.

**Definition 1.5 (The first bilinear coordinate).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.B1`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.B1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For i,a,b,x,y, B1(i,a,b,x,y) is ax+by when i is false and ax−by when i is true. The subscript here labels a coordinate of the bilinear map, not the choice of group.

**Definition 1.6 (The second bilinear coordinate).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.B2`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.B2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For i,a,b,x,y,z, B2(i,a,b,x,y,z) is ay+bz when i is false and bx+ay when i is true. Together B1 and B2 define the vector B(i,v,w).

**Definition 1.7 (The semidirect-product multiplication).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.mulS`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.mulS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For p=(v,w,c,e) and q=(v′,w′,c′,e′) in S(i), put σ=sign(e). Their product is (v+v′,w+σw′,c+σc′+σB(i,v,w′),e xor e′). Thus the normal subgroup with e=false has bilinear multiplication (v,w,c)(v′,w′,c′)=(v+v′,w+w′,c+c′+B(i,v,w′)), and the nontrivial Boolean element acts by (v,w,c)↦(v,−w,−c).

**Definition 1.8 (The identity).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.oneS`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.oneS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each Boolean i, oneS(i) is (0,0,0,0,0,0,0,false). It is the identity for mulS.

**Definition 1.9 (The inverse).**

Lean statement: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.invS`

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.invS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For p=(v,w,c,e) and σ=sign(e), invS(p) is (−v,−σw,−σc+σB(i,v,w),e). Bilinearity proves associativity, and these identity and inverse formulas give the actual Group structure on S(i).

**Definition 1.10 (The fixed-pair implication).**

$$claim = \left((\operatorname{card}\left(G\right) = 4374 \land \left(\operatorname{card}\left(H\right) = 4374 \land \left(\forall m \in \mathbb{Z},\; \exists f \in \operatorname{Equiv}\left(G, H\right),\; \forall p \in G,\; \operatorname{f}\left(p^{m}\right) = \operatorname{f}\left(p\right)^{m}\right)\right)) \Rightarrow (\exists f \in \operatorname{Equiv}\left(G, H\right),\; \forall p \in G,\; \operatorname{f}\left(p^{2}\right) = \operatorname{f}\left(p\right)^{2} \land \operatorname{f}\left(p^{3}\right) = \operatorname{f}\left(p\right)^{3})\right)$$

*Formalization.* `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In this formula G=S(false), H=S(true), Equiv(G,H) is the type of bijections between the underlying carriers, card is finite cardinality, and Z is the integers. Powers use the group operations just defined. The premise requires a possibly different bijection for each integer m, including zero and negative exponents. The conclusion requires one bijection preserving both natural powers two and three. This implication is posed for this fixed pair, not asserted as a conjecture of an external author.

**Theorem 1.11 (Separate conjugacy does not imply joint conjugacy).**

$$\neg ((\operatorname{card}\left(G\right) = 4374 \land \left(\operatorname{card}\left(H\right) = 4374 \land \left(\forall m \in \mathbb{Z},\; \exists f \in \operatorname{Equiv}\left(G, H\right),\; \forall p \in G,\; \operatorname{f}\left(p^{m}\right) = \operatorname{f}\left(p\right)^{m}\right)\right)) \Rightarrow (\exists f \in \operatorname{Equiv}\left(G, H\right),\; \forall p \in G,\; \operatorname{f}\left(p^{2}\right) = \operatorname{f}\left(p\right)^{2} \land \operatorname{f}\left(p^{3}\right) = \operatorname{f}\left(p\right)^{3}))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof establishes the entire premise and disproves the conclusion. Both actual groups have order 4374. Every integer-power map on G is conjugate to the corresponding map on H, but no bijection preserves both squares and cubes. In particular no single bijection preserves all integer powers.

Replace the central coordinate c by c+B(i,v,w). This is an invertible change of coordinates, not a group isomorphism between G and H. Direct calculations relate the actual squares, cubes and inverses to their expressions in these centered coordinates. The identity between centered carriers yields one bijection preserving the identity, cubes and inverses. A second bijection changes w on the e=true part by an invertible map depending on v, chosen so that B(true,v,w′)=B(false,v,w). The case v=0 is included. This bijection preserves squares and therefore fourth powers. Every element has sixth power one, so reduction modulo six supplies conjugacies for every integer exponent, including negative integers.

For a nonidentity involution u, define N(u)={x squared : x cubed=u}. A bijection preserving squares and cubes must preserve nonidentity involutions, these neighborhoods, and equality of neighborhoods. In G, the class of nonidentity involutions with a given neighborhood has nine elements; in H it has twenty-seven. The class descriptions follow from the actual coordinates and explicit bijections with F squared and F cubed. Transporting a class through a common square-cube bijection would equate these cardinalities, which is impossible.

The argument uses the classical bilinear central extension and its sign action, but constructs the power conjugacies directly. It does not assert the detailed enumeration of every functional-graph component or the classification of all finite groups with this separation.

## References

- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.B1`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.B2`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.F`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.S`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.claim`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.invS`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.mulS`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.oneS`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.productEquiv`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.result`
- Truth anchor: `D5/S3/FiniteGroups/PowerMaps/PowerMapSeparation.sign`
