# Arbitrary-Index Constrained Product

## Abstract

A common-source constrained product of arbitrary many actual metric extensions has shadowing under positive expansivity.

**Theorem 1.1 (Every observation has finite support).**

$$\begin{aligned}\forall I: Type, \forall Y: I \Rightarrow Type,\\{}[\forall i: I, \operatorname{MetricSpace}(\operatorname{Y}(i))]\\\forall S: \operatorname{Set}(\operatorname{Product}(Y)), \forall E: \operatorname{Set}(\operatorname{Pair}(S)),\\\operatorname{Entourage}(S, E) \Rightarrow\\\exists F: \operatorname{Finset}(I), eps: I \Rightarrow \mathbb{R},\\\operatorname{PositiveOn}(eps, F) \land \operatorname{CylinderImplies}(S, F, eps, E)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ConstrainedProduct.finite_support_entourage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

I is any set-index type, Y(i) any dependent metric family, S any product subspace, and E any entourage on S. There are a finite F and real eps(i)>0 for i in F such that, for every a,b in S, all inequalities dist(a(i),b(i))<eps(i) on F imply (a,b) in E. Subtype uniformity, Pi.uniformity, Filter.HasBasis.iInf' and the metric distance basis produce this implication. Neither I nor F must be nonempty.

**Theorem 1.2 (Shadowing in the actual constrained subspace).**

$$\begin{aligned}\forall I: Type, \forall X: Type, [\operatorname{UniformSpace}(X)] [\operatorname{CompactSpace}(X)]\\\forall B: I \Rightarrow Type, \forall Y: I \Rightarrow Type,\\{}[\forall i: I, \operatorname{MetricSpace}(\operatorname{B}(i))] [\forall i: I, \operatorname{MetricSpace}(\operatorname{Y}(i))] [\forall i: I, \operatorname{CompactSpace}(\operatorname{Y}(i))]\\\forall pi: \operatorname{DependentMap}(I, X, B), \forall p: \operatorname{CoordinateMap}(I, Y, B),\\\operatorname{CoordinateContinuous}(pi, p) \Rightarrow\\\operatorname{SeparatesPoints}(pi) \Rightarrow\\\operatorname{CoordinateSurjective}(p) \Rightarrow\\\forall f: X \Rightarrow X, \forall d: \operatorname{CoordinateEndomorphism}(B), \forall g: \operatorname{CoordinateEndomorphism}(Y),\\\operatorname{CoordinateSemiconjugacies}(pi, p, f, d, g) \Rightarrow\\\operatorname{HasShadowing}(f) \land \operatorname{CoordinateShadowing}(g) \land \operatorname{CoordinatePositiveExpansivity}(d) \Rightarrow\\\operatorname{HasShadowing}(\operatorname{CommonSourceDynamics}(pi, p, f, d, g))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ConstrainedProduct.constrained_product_hasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CoordinateContinuous means that every pi(i):X to B(i) and p(i):Y(i) to B(i) is continuous. CoordinateSurjective means every p(i) is onto. CoordinateSemiconjugacies asserts pi(i) f=d(i) pi(i) and p(i) g(i)=d(i) p(i). CoordinateShadowing and CoordinatePositiveExpansivity quantify over all i. No source or coordinate dynamics is required to be onto. The supplied metric extension spaces Y(i), their compactness and shadowing, and the positive expansive factors B(i), are parameters. No paper extension theorem is treated as an existing Lean instance.

Z consists of y in the product of Y(i) for which there exists one x with p(i)(y(i))=pi(i)(x) for every i. Separation makes x unique. For an entourage E on Z, finite_support_entourage selects F and tolerances. For every i in F, positive_expansivity_source_relative derives the exact-fibre tracing controls before the sequence is given. A finite intersection of pulled-back base observations and the projection's uniform continuity give the pseudo-orbit control. One base shadowing point x is chosen. The controlled coordinates trace in the exact fibres over pi(i)(x); uncontrolled coordinates are filled in those same fibres by choice. Their tuple lies in Z and E-traces at every natural time.

**Theorem 1.3 (Topology, projection and simultaneous whole orbits).**

$$\begin{aligned}\forall I: Type, \forall X: Type, [\operatorname{TopologicalSpace}(X)] [\operatorname{CompactSpace}(X)][\operatorname{TTwoSpace}(X)]\\\forall B: I \Rightarrow Type, \forall Y: I \Rightarrow Type,\\{}[\forall i: I, \operatorname{MetricSpace}(\operatorname{B}(i))] [\forall i: I, \operatorname{MetricSpace}(\operatorname{Y}(i))] [\forall i: I, \operatorname{CompactSpace}(\operatorname{Y}(i))][\forall i: I, \operatorname{TotallyDisconnectedSpace}(\operatorname{Y}(i))]\\\forall pi: \operatorname{DependentMap}(I, X, B), \forall p: \operatorname{CoordinateMap}(I, Y, B),\\\operatorname{CoordinateContinuous}(pi, p) \Rightarrow\\\operatorname{SeparatesPoints}(pi) \Rightarrow\\\operatorname{CoordinateSurjective}(p) \Rightarrow\\\forall f: X \Rightarrow X, \forall d: \operatorname{CoordinateEndomorphism}(B), \forall g: \operatorname{CoordinateEndomorphism}(Y),\\\operatorname{CoordinateSemiconjugacies}(pi, p, f, d, g) \Rightarrow\\\operatorname{HasShadowing}(f) \land \operatorname{CoordinateShadowing}(g) \land \operatorname{CoordinatePositiveExpansivity}(d) \Rightarrow\\\operatorname{CoordinateContinuous}(g) \Rightarrow\\Z=\operatorname{CommonSource}(pi, p), q=\operatorname{CommonSourceMap}(pi, p),\\G=\operatorname{CommonSourceDynamics}(pi, p, f, d, g)\\\operatorname{IsClosed}(\operatorname{CommonSourceSet}(pi, p)) \land\\\operatorname{CompactSpace}(Z) \land \operatorname{TTwoSpace}(Z) \land \operatorname{TotallyDisconnectedSpace}(Z) \land\\\operatorname{Continuous}(q) \land \operatorname{Surjective}(q) \land \operatorname{Continuous}(G) \land\\\operatorname{Semiconj}(q, G, f) \land \operatorname{HasShadowing}(G) \land\\\operatorname{WholeOrbitCoding}(X, I, Z, q, G, p, pi, f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ConstrainedProduct.constrained_product_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

X is compact Hausdorff; the compatible uniformity is introduced explicitly inside the proof. Each Y(i) is also totally disconnected. The exact conclusion is a conjunction: commonSourceSet is closed; Z is compact, Hausdorff and totally disconnected; q is continuous and onto; G is continuous; q semiconjugates G to f; and G has the existing finite-open-cover shadowing property. WholeOrbitCoding is: for every x in X there is z in Z with q(z)=x and, for every i and every natural n including zero, p(i)((G^n(z))(i))=pi(i)(f^n(x)). Compact Hausdorff totally disconnected spaces have the Mathlib clopen basis. Z is the inverse image of the compact range of the separating coordinate embedding. Continuity of q follows through that embedding, not from continuity of an arbitrary choice function. Tychonoff and ordinary choice are represented by Mathlib and Classical.choice.

Empty and singleton index types, empty finite support and empty source are included. For an empty index, separation forces a nonempty source to be a singleton. No inverse orbit or orbit-surjectivity is used. Onto factor maps pi(i), compactness and shadowing of B(i), and continuity of f and d(i) may be added to recover the approved system telescope; the proof does not require these extra premises. Peng Q5.1 and Q5.2 remain open here. Without positive expansivity, the unpaid obligation is one joint source point lying in every finite coordinate's prescribed-fibre tracer set, with the control chosen before each pseudo-orbit. ALP and vertex surjectivity do not pay it. No novelty or priority is claimed.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ConstrainedProduct.constrained_product_extension`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ConstrainedProduct.constrained_product_hasShadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ConstrainedProduct.finite_support_entourage`
- Dependency: [D5/S1/Dynamics/Shadowing/UniformTracing](UniformTracing.md)
