# Moore's theorem for strongly irreducible subshifts of finite type

## Abstract

A finite collision in a finite-type subshift can be replaced uniformly within that same subshift; relative pattern counting gives Moore's implication for strongly irreducible subshifts over arbitrary right-counting amenable groups.

Let G be an arbitrary group and let A be a finite discrete alphabet, in independent universes. X is a native closed invariant subshift, and tau is a continuous equivariant endomorphism of its actual carrier Cfg(X). All products have the displayed order. There is no countability, finite generation or commutativity hypothesis.

SI(X,Delta) says that any two occurring patterns on finite supports F and K have a common realization in X whenever F*Delta inverse is disjoint from K. The original finite Delta may be empty or asymmetric. The counting hypothesis gives G the top measurable space and assumes that maxFoelner(G opposite,Measure.count) is nontrivial. The action is (op e) acting on g by g*e. Finite nonempty shapes are taken from this filter over arbitrary subsets of G, without choosing a countable sequence.

**Definition 1.1 (A finite family of native forbidden patterns).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\operatorname{IsFiniteType}(X) \iff \exists a: A,letI \operatorname{Inhabited}(A):=\operatorname{Inhabited.mk}(a),\exists B: \operatorname{Finset}(\operatorname{Pattern}(A, G)),\operatorname{carrier}(X) = \operatorname{mulForbidden}(B)}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/FiniteTypeMoore.IsFiniteType` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The padding value a is chosen existentially. Every member of B has its own arbitrary finite support and gives a forbidden word on that support. A configuration belongs to X exactly when no member of B occurs at any left translate. Any finitely supported word is represented by padding it with a outside its support; occurrences inspect only the support. An empty family defines the full shift. An empty-support forbidden word has every translate as an occurrence and hence defines an empty carrier. No uniform defining-window premise, algorithm or inhabitance instance is supplied separately.

**Theorem 1.2 (Uniform complete-image replacement in the same subshift).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{[\operatorname{Finite}(A)],[\operatorname{DiscreteTopology}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{(\operatorname{IsFiniteType}(X)) \Rightarrow \forall tau: (\operatorname{Cfg}(X)) \to \operatorname{Cfg}(X),(\operatorname{Continuous}(tau)) \Rightarrow ((\forall g: G,\forall z: \operatorname{Cfg}(X),\operatorname{tau}(\operatorname{paperShift}(X, g, z)) = \operatorname{paperShift}(X, g, \operatorname{tau}(z)))) \Rightarrow \forall x: \operatorname{Cfg}(X),\forall y: \operatorname{Cfg}(X),(x \neq y) \Rightarrow (\operatorname{Set.Finite}(\{g:G \mid \operatorname{x}(g) \neq \operatorname{y}(g)\})) \Rightarrow (\operatorname{tau}(x) = \operatorname{tau}(y)) \Rightarrow \exists C: \operatorname{Finset}(G),(\operatorname{Nonempty}(C)) \land (\exists p: (C) \to A,\exists q: (C) \to A,(p \neq q) \land ((p \in \operatorname{PatX}(X, C)) \land ((q \in \operatorname{PatX}(X, C)) \land (\forall t: G,\forall z: \operatorname{Cfg}(X),((\forall c: C,\operatorname{z}(t * c) = \operatorname{p}(c))) \Rightarrow \exists zprime: \operatorname{Cfg}(X),(\forall c: C,\operatorname{zprime}(t * c) = \operatorname{q}(c)) \land ((\forall g: G,(\neg(g \in \operatorname{tile}(t, C))) \Rightarrow \operatorname{zprime}(g) = \operatorname{z}(g)) \land (\operatorname{tau}(zprime) = \operatorname{tau}(z)))))))}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/FiniteTypeMoore.collision_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Neither strong irreducibility nor amenability is used. Let D be the finite disagreement set, and let S contain the finite memory of tau and every forbidden support. Take the finite collar C=D union D*S inverse*S, retaining the order d*s inverse*r. Put p=x restricted to C and q=y restricted to C; D is nonempty and contained in C, so p and q are distinct occurring words. For a configuration agreeing with x on C, replace C by y. A translated forbidden support touching D lies wholly in C and therefore sees y; a support missing D sees the original configuration. Both avoid every forbidden word. The same dichotomy for a translated memory window gives the entire equality of tau-images, using the actual collision tau(x)=tau(y). Equivariance transports the construction to each translate t*C. The result stays inside X, equals q on the translated support, and agrees with the original configuration at every point outside it. To combine the two local tests, extend the identity output of tau from occurring memory words and pair it with the Boolean test for avoiding all forbidden words. This defines a full-shift local rule on A times Bool. On a configuration encoded from X its complete output is (tau(z)(g),true) at every g. AmenableGardenOfEden.localMap_piecewise_of_collar preserves this paired output. The Boolean coordinate recovers membership in X before the first coordinate recovers equality of the native tau-images.

For finitely many disjoint C-tiles, replace p by q wherever p occurs. Each replacement preserves membership and the complete image, and disjointness preserves exclusions already obtained. Choose such a representative for each actual image pattern on F. Its restriction to U determines the image pattern whenever F*M is contained in U. This injects the actual image patterns into the occurring U-patterns that avoid p on every selected tile; it is an input-avoidance comparison.

**Theorem 1.3 (Surjectivity implies preinjectivity).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{[\operatorname{Finite}(A)],[\operatorname{DiscreteTopology}(A)],}\\{\operatorname{MeasurableSpace}(G):=\operatorname{top}(),}\\{\operatorname{NeBot}(\operatorname{maxFoelner}((G)^{\mathrm{op}}, \operatorname{Measure.count}(G))) \Rightarrow}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\operatorname{Set.Nonempty}(\operatorname{carrier}(X)) \Rightarrow}\\{(\exists Delta: \operatorname{Finset}(G),\operatorname{SI}(X, Delta)) \Rightarrow}\\{\operatorname{IsFiniteType}(X) \Rightarrow}\\{\forall tau: (\operatorname{Cfg}(X)) \to \operatorname{Cfg}(X),}\\{\operatorname{Continuous}(tau) \Rightarrow}\\{(\forall g: G,\forall z: \operatorname{Cfg}(X),\operatorname{tau}(\operatorname{paperShift}(X, g, z)) = \operatorname{paperShift}(X, g, \operatorname{tau}(z))) \Rightarrow}\\{\operatorname{Function.Surjective}(tau) \Rightarrow}\\{(\forall x: \operatorname{Cfg}(X),\forall y: \operatorname{Cfg}(X),(\operatorname{Set.Finite}(\{g:G \mid \operatorname{x}(g) \neq \operatorname{y}(g)\})) \Rightarrow (\operatorname{tau}(x) = \operatorname{tau}(y)) \Rightarrow x = y)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/FiniteTypeMoore.moore` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write E=C*Delta inverse, enlarging Delta to contain the identity. Pack disjoint E-tiles with centers in a finite right-Foelner shape B. Put U=B*K, where the fixed finite K contains the identity, E and the memory M. This supplies containment of the tiles and B*M in U. The relative pattern bound, with rho=card(PatX(X,E)), gives card(ImagePat(X,tau,B))*rho^tiles at most card(PatX(X,U))*(rho-1)^tiles. Surjectivity identifies the image language with the language of X on B. Padding from B to U costs at most card(A) raised to card(U minus B). Nonemptiness permits cancellation. Packing gives positive tile density, while the right-Foelner boundary makes card(U minus B)/card(B) tend to zero. The relative limit contradiction also covers rho=1. Thus a nontrivial finite collision is impossible. Combining this implication with StronglyIrreducibleMyhill.myhill gives the Garden-of-Eden equivalence for this same X and tau.

Finite and trivial groups are included through the same right-counting filter. Singleton alphabets and singleton carriers need no separate cardinality lower bound. The empty alphabet remains quantified; a nonempty carrier would internally supply a letter by evaluation at the identity, so that case has no instance. All defining supports and memory windows may be empty or asymmetric. These mathematical implications make no publication-priority claim.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteTypeMoore.IsFiniteType`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteTypeMoore.collision_replacement`
- Truth anchor: `D5/S1/Dynamics/Symbolic/FiniteTypeMoore.moore`
- Dependency: [D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill](StronglyIrreducibleMyhill.md)
