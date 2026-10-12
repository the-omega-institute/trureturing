# All commuting history homeomorphisms and derived whole-ray geometry

## Abstract

All commuting history homeomorphisms and derived whole-ray geometry.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (The full subgroup has no supplied window or beam-support field).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right),\; \forall f \in \operatorname{Homeomorph}\left(\operatorname{History}\left(G\right), \operatorname{History}\left(G\right)\right),\; f \in \operatorname{fullAutSubgroup}\left(G\right) \Leftrightarrow \left(\forall x \in \operatorname{History}\left(G\right),\; f\left(\operatorname{shift}\left(G, x\right)\right) = \operatorname{shift}\left(G, f\left(x\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.fullAutSubgroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

homeomorph(h) means h.val for a member of FullAut G, the subtype fullAutSubgroup G of History G homeomorphisms. Membership requires exactly f(shift x)=shift(f x) for all histories. Multiplication is (g*h)(x)=g(h(x)); inversion is the actual homeomorphism inverse. The finite vertex and edge types have their given discrete topologies. No endpoint preservation, action support, window, entropy, mixing or essentiality is part of this membership condition.

**Theorem 1.2 (Compactness derives both windows for every full automorphism).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right),\; \forall h \in \operatorname{FullAut}\left(G\right),\; \exists a \in Nat, b \in Nat, c \in Nat, d \in Nat,\; \operatorname{Controls}\left(G, \operatorname{homeomorph}\left(h\right), a, b\right) \land \operatorname{Controls}\left(G, \operatorname{symm}\left(\operatorname{homeomorph}\left(h\right)\right), c, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.fullAut_has_two_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Controls G f a b means forall x y : History G, forall k:Int, if forall t:Int with k-a<=t<=k+b the edges x t and y t agree, then (f x) k=(f y) k. All radii are natural, and the displayed inverse is h.val.symm. The legal history subspace is closed in a finite discrete product, hence compact. Continuity of the output at zero gives local finite-coordinate cylinders; a finite subcover gives uniform finite control. Commutation with all integer translates transfers this to every k. Apply the same argument to h inverse; locality is a consequence, not an assumed domain restriction.

**Theorem 1.3 (An image contains whole intrinsic rays at a controlled cut).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), hG \in \operatorname{Essential}\left(G\right),\; \forall h \in \operatorname{FullAut}\left(G\right), a \in Nat, b \in Nat, c \in Nat, d \in Nat, hab \in \operatorname{Controls}\left(G, \operatorname{homeomorph}\left(h\right), a, b\right), hcd \in \operatorname{Controls}\left(G, \operatorname{symm}\left(\operatorname{homeomorph}\left(h\right)\right), c, d\right), alpha \in \operatorname{History}\left(G\right), n \in Int,\; \operatorname{AtCut}\left(G, \operatorname{image}\left(\operatorname{homeomorph}\left(h\right), \operatorname{ray}\left(G, alpha, n\right)\right), \operatorname{laterCut}\left(n, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.image_ray_atCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

image denotes the entire Set.image, not the images of selected representatives. laterCut(n,d)=n+(d:Int). The forward window places the image in ray G (h alpha) (n-b). The inverse window proves that every image point brings its whole (n+d)-ray, allowing every legal future. Finite numbered refinement between n-b and n+d bounds intrinsic pieces by Delta^(b+d). image_isBeam extends this to any finite intrinsic beam; the two displayed window hypotheses are derived for every h by fullAut_has_two_windows.

**Theorem 1.4 (The conjugate maps an entire intrinsic ray onto the entire target ray).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right),\; \forall h \in \operatorname{FullAut}\left(G\right), a \in Nat, b \in Nat, c \in Nat, d \in Nat, hab \in \operatorname{Controls}\left(G, \operatorname{homeomorph}\left(h\right), a, b\right), hcd \in \operatorname{Controls}\left(G, \operatorname{symm}\left(\operatorname{homeomorph}\left(h\right)\right), c, d\right), alpha \in \operatorname{History}\left(G\right), beta \in \operatorname{History}\left(G\right), n \in Int, ep \in \operatorname{endpoint}\left(G, alpha, n\right) = \operatorname{endpoint}\left(G, beta, n\right), y \in \operatorname{image}\left(\operatorname{homeomorph}\left(h\right), \operatorname{ray}\left(G, alpha, n\right)\right),\; \operatorname{image}\left(\operatorname{conjugateSplice}\left(G, h, alpha, beta, n, ep\right), \operatorname{restrictedRay}\left(G, y, \operatorname{conjugateCut}\left(n, a, b, d\right)\right)\right) = \operatorname{restrictedRay}\left(G, \operatorname{conjugateSplice}\left(G, h, alpha, beta, n, ep\right)\left(y\right), \operatorname{conjugateCut}\left(n, a, b, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.conjugateSplice_rayImage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

conjugateSplice is h composed with spliceEquiv(alpha,beta,n,ep) and h inverse, restricted to the two actual image subsets. conjugateCut(n,a,b,d)=n+a+b+d with integer casts. restrictedRay(y,ell) is {z in the appropriate image subtype | z.val belongs to ray G y.val ell}; on the right it is a subset of h image of beta's ray. The theorem is exact equality of these sets.

The conjugate keeps every future edge k>n+a. The forward and inverse Controls force equal pasts through ell to map to equal pasts through ell. Conjugating the reverse splice proves reverse inclusion. At ell the next edge agrees, so legal seams DERIVE endpoint equality. conjugateSplice_on_ray identifies each restriction with the actual past splice. With Essential G, conjugatePartsEquiv and its endpoint theorem give the endpoint-preserving bijection needed for quotient compatibility.

**Theorem 1.5 (The actual shift decreases every integer cut by one).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right),\; \forall alpha \in \operatorname{History}\left(G\right), n \in Int,\; \operatorname{image}\left(\operatorname{shiftMap}\left(G\right), \operatorname{ray}\left(G, alpha, n\right)\right) = \operatorname{ray}\left(G, \operatorname{shift}\left(G, alpha\right), \operatorname{previousCut}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.shift_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

shiftMap G is the function FiniteWindowTableCriterion.shift G, and shift G alpha evaluates alpha at k+1. previousCut(n)=n-1. The inverse reindexes at k-1, proving equality for the whole set. shift_ray_endpoint keeps G.target(alpha n) at the new cut. The statement covers cut zero and negative cuts.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.conjugateSplice_rayImage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.fullAutSubgroup`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.fullAut_has_two_windows`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.image_ray_atCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.shift_ray`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamGeometry](StandardBeamGeometry.md)
