# The ordered free complex of a set cover

## Abstract

The actual ordered free complex of an arbitrary set cover contracts onto the free object on its points.

There are three independent universes: C has objects in Type u and morphisms in Type v; the linearly ordered index type iota and the point type A lie in Type w. HasCoproducts(w,C) means that every Type w-indexed family has its existing categorical coproduct. The coefficient is an arbitrary object R. Preadditivity supplies addition and integer signs on morphisms. A zero object is used for the complex concentrated in degree zero. No finiteness or nonemptiness assumption is made on iota or A.

**Definition 1.1 (The actual intersection objects).**

$$\begin{aligned}\forall C: \operatorname{Type}\left(u\right), [\operatorname{Category}\left(v, C\right)] [\operatorname{HasCoproducts}\left(w, C\right)] \\\forall iota: \operatorname{Type}\left(w\right), \forall A: \operatorname{Type}\left(w\right), \\\forall R: C, \forall P: iota \to \operatorname{Set}\left(A\right), \\\operatorname{freeFunctor}\left(R, P\right): \operatorname{Functor}\left(\operatorname{op}\left(\operatorname{Finset}\left(iota\right)\right), C\right)\\\forall s: \operatorname{Finset}\left(iota\right), \operatorname{obj}\left(\operatorname{freeFunctor}\left(R, P\right), \operatorname{op}\left(s\right)\right) = \operatorname{coproduct}\left(\operatorname{intersectionPoints}\left(P, s\right), R\right)\end{aligned}$$

*Formalization.* `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.freeFunctor` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Ordered free Cech complexes of set covers*. URL: <https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/OrderedCech/Cover.lean>.

*Commentary.*

For a finite set s of indices, intersectionPoints(P,s) is the subtype of points a of A such that a belongs to P(i) for every i in s. The empty intersection has all of A as its points. The object at s is the coproduct of one copy of R for each such point. For t contained in s, the map from the object at s to the object at t is induced by the actual inclusion of intersection points. It sends each point summand to the summand of the same point.

**Definition 1.2 (The ordered deletion differential).**

$$\begin{aligned}\forall C: \operatorname{Type}\left(u\right), [\operatorname{Category}\left(v, C\right)] [\operatorname{HasCoproducts}\left(w, C\right)] \\\forall iota: \operatorname{Type}\left(w\right), \forall A: \operatorname{Type}\left(w\right), \\\forall R: C, \forall P: iota \to \operatorname{Set}\left(A\right), \\{}[\operatorname{Preadditive}\left(C\right)] [\operatorname{LinearOrder}\left(iota\right)] \\\operatorname{complex}\left(R, P\right): \operatorname{ChainComplex}\left(C, Nat\right)\\\forall p: Nat, \operatorname{X}\left(\operatorname{complex}\left(R, P\right), p\right) = \operatorname{coproduct}\left(\operatorname{finsetsOfCard}\left(iota, \operatorname{succ}\left(p\right)\right), \operatorname{intersectionFreeObjects}\left(R, P\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.complex` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Ordered free Cech complexes of set covers*. URL: <https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/OrderedCech/Cover.lean>.

*Commentary.*

For every natural degree p, finsetsOfCard(iota,succ(p)) is the subtype of finite index sets with p+1 elements; intersectionFreeObjects(R,P) is the preceding functor evaluated at such a set. On the summand (s,a) in degree p+1 the differential is the sum over i in s of the summand (s without i,a), multiplied by (-1) to the number of j in s with j<i. This is the increasing-order finite-set deletion sign. The composite of consecutive differentials vanishes in every natural degree. Increasing enumerations identify successive deletions with the Fin simplicial identity, so the alternating double-sum cancellation applies to the actual intersection inclusions.

**Definition 1.3 (The specified augmentation).**

$$\begin{aligned}\forall C: \operatorname{Type}\left(u\right), [\operatorname{Category}\left(v, C\right)] [\operatorname{HasCoproducts}\left(w, C\right)] \\\forall iota: \operatorname{Type}\left(w\right), \forall A: \operatorname{Type}\left(w\right), \\\forall R: C, \forall P: iota \to \operatorname{Set}\left(A\right), \\{}[\operatorname{Preadditive}\left(C\right)] [\operatorname{LinearOrder}\left(iota\right)] \\{}[\operatorname{HasZeroObject}\left(C\right)] \\\operatorname{augmentation}\left(R, P\right): \operatorname{Hom}\left(\operatorname{complex}\left(R, P\right), \operatorname{singleZero}\left(\operatorname{coproduct}\left(A, R\right)\right)\right)\\\forall s: \operatorname{finsetsOfCard}\left(iota, 1\right), \forall a: \operatorname{intersectionPoints}\left(P, s\right), \operatorname{degreeZeroPointImage}\left(\operatorname{augmentation}\left(R, P\right), s, a\right) = \operatorname{pointInclusion}\left(\operatorname{val}\left(a\right), \operatorname{coproduct}\left(A, R\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.augmentation` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Ordered free Cech complexes of set covers*. URL: <https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/OrderedCech/Cover.lean>.

*Commentary.*

singleZero is the chain complex concentrated at zero with object coproduct(A,R). Here degreeZeroPointImage denotes composition with the two actual summand inclusions for a singleton s and a point a belonging to its intersection. The augmentation sends this summand to the a summand of coproduct(A,R). Its components in positive degrees are zero. The two faces of every degree-one summand have the same point image and opposite signs, so this is a chain map. Its definition uses the family P without requiring a cover equation or a contraction.

**Theorem 1.4 (A homotopy inverse for the same augmentation).**

$$\begin{aligned}\forall C: \operatorname{Type}\left(u\right), [\operatorname{Category}\left(v, C\right)] [\operatorname{HasCoproducts}\left(w, C\right)] \\\forall iota: \operatorname{Type}\left(w\right), \forall A: \operatorname{Type}\left(w\right), \\\forall R: C, \forall P: iota \to \operatorname{Set}\left(A\right), \\{}[\operatorname{Preadditive}\left(C\right)] [\operatorname{LinearOrder}\left(iota\right)] \\{}[\operatorname{HasZeroObject}\left(C\right)] \\\operatorname{iUnion}\left(P\right) = \operatorname{univ}\left(A\right) \Rightarrow\\\exists E: \operatorname{HomotopyEquiv}\left(\operatorname{complex}\left(R, P\right), \operatorname{singleZero}\left(\operatorname{coproduct}\left(A, R\right)\right)\right), \operatorname{hom}\left(E\right) = \operatorname{augmentation}\left(R, P\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.augmentation_homotopy_equiv` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Ordered free Cech complexes of set covers*. URL: <https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/OrderedCech/Cover.lean>.

*Commentary.*

Assume that the union of P(i) over all iota is A. Choose for each point a an index c(a) with a in P(c(a)). The section sends a to the summand ({c(a)},a). In degree p the homotopy inserts c(a) into s with sign (-1) to the number of indices of s strictly less than c(a); it is zero if c(a) is already in s. These maps are defined by coproduct descent, without finite-support or finite-cover assumptions.

Write composition in categorical order. The section followed by the augmentation is the identity. In degree zero, H(0) followed by d(0) is the identity minus augmentation followed by section. In degree p+1, d(p) followed by H(p), plus H(p+1) followed by d(p+1), is the identity. If c(a) is present, all cone-face terms vanish except deletion of c(a), whose total sign is +1. If c(a) is absent, deletion of the inserted vertex contributes (s,a), and all other terms cancel against the homotopy after deletion. At degree zero the remaining cone face is exactly the chosen section. The native chain-homotopy construction assembles these identities into E, whose forward map is exactly the independently defined augmentation.

The result includes empty intersections, zero coefficient objects, infinite index and point types, and empty covers whenever their union is A. If iota is empty, the cover equation forces A to be empty. There is no topology, good-cover, abelian-category, module, field, extra-exactness or supplied-contraction hypothesis. This statement concerns the ordered free complex of a set cover; no singular-chain total-complex comparison is asserted.

**Definition 1.5 (Maps on the same intersection generators).**

Lean statement: `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.map`

*Formalization.* `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.map` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For point types A and B, families P and Q with the same ordered index type, and a function f from A to B taking P(i) into Q(i) for every i, there is a chain map from the ordered free complex of P to that of Q. It sends each generator (s,a) to (s,f(a)). The finite index set and every deletion sign are preserved. These maps preserve identity and composition.

## References

- Truth anchor: `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.augmentation`
- Truth anchor: `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.augmentation_homotopy_equiv`
- Truth anchor: `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.complex`
- Truth anchor: `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.freeFunctor`
- Truth anchor: `D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.map`
