# Finite Observations of Shadowing Sources

## Abstract

Every continuous observation into a finite discrete alphabet of a finite-open-cover shadowing source has an exact entire finite graph language.

**Definition 1.1 (All complete forward graph paths).**

$$\begin{aligned}\forall V: Type u, A: Type v, E: V \Rightarrow V \Rightarrow Prop, l: V \Rightarrow A,\\\operatorname{graphLanguage}(E, l) = \{w: \mathbb{N} \Rightarrow A \mid \exists p: \mathbb{N} \Rightarrow V, \forall n: \mathbb{N}, E(p(n), p(n+1)) \land l(p(n)) = w(n)\}.\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Shadowing/FiniteObservationSofic.graphLanguage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary vertex type V, alphabet A, directed edge relation E and vertex label l, graphLanguage(E,l) consists of words w for which one entire path p satisfies E(p(n),p(n+1)) and l(p(n))=w(n) for every natural n. All vertices are allowed as initial vertices, and time zero is included. Vertices with no predecessor are retained; vertices with no infinite continuation produce no word.

**Definition 1.2 (Exact finite graph presentation).**

$$\begin{aligned}\forall A: Type u, S: \operatorname{Set}(\mathbb{N} \Rightarrow A),\\\operatorname{IsSofic}(S) \Leftrightarrow \exists n: \mathbb{N}, E: \operatorname{Fin}(n) \Rightarrow \operatorname{Fin}(n) \Rightarrow Prop, l: \operatorname{Fin}(n) \Rightarrow A, S = \operatorname{graphLanguage}(E, l).\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Shadowing/FiniteObservationSofic.IsSofic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsSofic(S) means that some natural n, a relation E on Fin n and a label map l:Fin n→A have S=graphLanguage(E,l). The equality concerns complete infinite words. It is stronger than finite-prefix realization or one-sided language inclusion. The n=0 graph is allowed and its language is empty.

**Theorem 1.3 (Finite observations preserve exact sofic histories).**

$$\begin{aligned}\forall X: Type u, [\operatorname{TopologicalSpace}(X)], A: Type v, [\operatorname{TopologicalSpace}(A)], [\operatorname{DiscreteTopology}(A)], [\operatorname{Finite}(A)],\\\forall f: X \Rightarrow X, a: X \Rightarrow A, \operatorname{Continuous}(a) \Rightarrow \operatorname{HasShadowing}(f) \Rightarrow \operatorname{IsSofic}(\operatorname{Set.range}(\operatorname{completeItinerary}(f, a))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteObservationSofic.finite_observation_isSofic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Let X be any topological space, f:X→X any self-map, and a:X→A continuous, where A is finite and discrete. Assume the exact HasShadowing notion imported from MittagLefflerInverseLimit: every finite open output cover C has a finite open control cover D, and every whole D-pseudo-orbit is C-shadowed by one point. Then the range of completeItinerary(f,a), x↦(n↦a(f^[n](x))), is sofic.

Take C to be all observation fibers a⁻¹{c}, including empty fibers, and choose a finite shadowing control cover D. Use D×A as the finite vertex type. There is an edge (U,c)→(V,d) exactly when one x lies in U with a(x)=c and f(x) lies in V with a(f(x))=d. Label (U,c) by c. Empty cells may be retained, since no complete path can use them.

A complete graph path has, at each time n, one edge witness x(n). Both f(x(n)) and x(n+1) lie in the next vertex's D-member, so these witnesses form one whole D-pseudo-orbit. Its C-tracer z has a(f^[n](z)) equal to the path label at every n. This proves graph-language soundness for whole histories. Conversely, for any actual source point x choose a D-member containing each f^[n](x); those vertices and source points give all edges and the exact observed word. A finite-carrier equivalence reindexes D×A as Fin n without changing either complete-path language. Together these prove exact equality.

The graph construction requires no compactness or separation of X and no continuity, surjectivity or invertibility of f. Off compact sources this finite-open-cover hypothesis should not be silently identified with metric or uniform shadowing, whose control covers can be infinite. For the original compact Hausdorff continuous source it is precisely the intended finite-cover formulation. Empty sources and alphabets are included by the same proof: any putative full graph path would yield a source edge witness, so the graph language is empty.

The noncompact qualification is substantive. In ordinary mathematics, the successor map on the natural numbers with the discrete metric has metric shadowing: an error tolerance below one forces exact orbits. Observe the mechanical word b(n)=floor((n+1)alpha)-floor(n alpha), choosing irrational alpha with 0<alpha<1. This is a continuous binary observation on that discrete source, and all its complete histories have irrational limiting frequency alpha. None is periodic, whereas a nonempty entire finite graph language contains a periodic cycle word. Hence this metric-shadowing source cannot satisfy the finite-cover HasShadowing premise. This comparison is ordinary explanatory mathematics, not an additional formalized metric-shadowing theorem in the present module.

The S1 statement writes the history as x↦(n↦a(f^[n](x))), the definitional expansion of the existing S3 completeItinerary, and reuses HasShadowing. Its retained Reg mirror imports the original history definition explicitly and checks the same statement by definitional equality. The mathematical S1 import closure contains no S3 dependency. Its full-history finite graph conclusion supports obstructions to proposed shadowing covers, but does not construct a single globally coherent family of Peng's finite-net arrays. Questions 5.1 and 5.2 remain unresolved here. No literature originality or solution-priority claim is attached to this graph mechanism. The conclusion is soficity of the observed image; no shadowing property of arbitrary image factors is asserted.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteObservationSofic.IsSofic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteObservationSofic.finite_observation_isSofic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteObservationSofic.graphLanguage`
- Dependency: [D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit](MittagLefflerInverseLimit.md)
