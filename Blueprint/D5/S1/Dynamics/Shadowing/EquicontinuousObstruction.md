# Equicontinuity and Exact Fibres

## Abstract

An equicontinuous connected subset obstructs universally prescribed-source tracing; compact contractions illustrate the boundary.

**Theorem 1.1 (orbit lifting clopen image).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)] [\operatorname{TTwoSpace}(X)]\\\forall Y: Type, [\operatorname{UniformSpace}(Y)] [\operatorname{CompactSpace}(Y)]\\\forall p: Y \Rightarrow X, \forall g: Y \Rightarrow Y, \forall f: X \Rightarrow X,\\\operatorname{Continuous}(p) \land \operatorname{Semiconj}(p, g, f) \Rightarrow\\\forall K: \operatorname{Set}(X),\\\operatorname{ForwardUniformEquicontinuity}(f, K) \Rightarrow\\\operatorname{OrbitLifting}(p, g, f) \Rightarrow\\\forall C: \operatorname{Set}(Y),\\\operatorname{IsClopen}(C) \Rightarrow\\\operatorname{IsClopen}(\operatorname{RelativeImage}(p, C, K))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.orbit_lifting_clopen_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ForwardUniformEquicontinuity(f,K) means UniformEquicontinuous(n ↦ (x:K ↦ f^n(x.val))) with codomain X. RelativeImage(p,C,K) is {x:K | x.val lies in p(C)}. C is compact, so its image is closed in Hausdorff X. The two clopen cells C and its complement give one diagonal entourage. OL and equicontinuity give a neighborhood of each point of the relative image whose lifts remain in C at time zero. No compactness or invariance of K is required here.

**Theorem 1.2 (orbit lifting clopen basis).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)] [\operatorname{TTwoSpace}(X)]\\\forall Y: Type, [\operatorname{UniformSpace}(Y)] [\operatorname{CompactSpace}(Y)][\operatorname{TTwoSpace}(Y)] [\operatorname{TotallyDisconnectedSpace}(Y)]\\\forall p: Y \Rightarrow X, \forall g: Y \Rightarrow Y, \forall f: X \Rightarrow X,\\\operatorname{Continuous}(p) \land \operatorname{Semiconj}(p, g, f) \Rightarrow\\\forall K: \operatorname{Set}(X),\\\operatorname{ForwardUniformEquicontinuity}(f, K) \Rightarrow\\\operatorname{Surjective}(p) \Rightarrow\\\operatorname{OrbitLifting}(p, g, f) \Rightarrow\\\operatorname{IsCompact}(K) \Rightarrow\\\operatorname{ClopenBasis}(K)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.orbit_lifting_clopen_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For compact K, the clopen relative images form a neighborhood basis. Given x in an open U of K, the image in X of K minus U is compact and closed. Separate its p-preimage from the entire closed fibre over x by a clopen C in compact Hausdorff totally disconnected Y. Surjectivity puts x in the relative image, and fibre avoidance puts that image inside U. This proves a basis of all clopens on K, hence zero-dimensionality.

**Theorem 1.3 (connected subset not source relative).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)] [\operatorname{TTwoSpace}(X)]\\\forall Y: Type, [\operatorname{UniformSpace}(Y)] [\operatorname{CompactSpace}(Y)][\operatorname{TTwoSpace}(Y)] [\operatorname{TotallyDisconnectedSpace}(Y)]\\\forall p: Y \Rightarrow X, \forall g: Y \Rightarrow Y, \forall f: X \Rightarrow X,\\\operatorname{Continuous}(p) \land \operatorname{Semiconj}(p, g, f) \Rightarrow\\\forall K: \operatorname{Set}(X),\\\operatorname{ForwardUniformEquicontinuity}(f, K) \Rightarrow\\\operatorname{Surjective}(p) \Rightarrow\\\operatorname{IsCompact}(K) \Rightarrow\\\operatorname{IsPreconnected}(K) \Rightarrow\\\operatorname{Nondegenerate}(K) \Rightarrow\\\neg \operatorname{SourceRelativeTracing}(p, g, f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.connected_subset_not_source_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nondegenerate(K) means there are two distinct points of the subtype K. SR implies OL by using exact orbits as pseudo-orbits for every control. OL would give a clopen basis, making K totally separated and totally disconnected. Preconnectedness would force its points to agree, contradicting nondegeneracy. No f-invariance of K is introduced.

**Theorem 1.4 (connected fixed orbit obstruction).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)] [\operatorname{TTwoSpace}(X)]\\\forall Y: Type, [\operatorname{UniformSpace}(Y)] [\operatorname{CompactSpace}(Y)][\operatorname{TTwoSpace}(Y)] [\operatorname{TotallyDisconnectedSpace}(Y)]\\\forall p: Y \Rightarrow X, \forall g: Y \Rightarrow Y, \forall f: X \Rightarrow X,\\\operatorname{Continuous}(p) \land \operatorname{Semiconj}(p, g, f) \Rightarrow\\\forall K: \operatorname{Set}(X),\\\operatorname{ForwardUniformEquicontinuity}(f, K) \Rightarrow\\\operatorname{Surjective}(p) \Rightarrow\\\operatorname{IsPreconnected}(K) \Rightarrow\\\operatorname{Nondegenerate}(K) \Rightarrow\\\operatorname{FixedOrbitFailure}(p, g, f, K)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.connected_fixed_orbit_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FixedOrbitFailure is the exact order: there are E in the upstairs uniformity and a in Y such that, for every D in the upstairs uniformity and every V in the downstairs uniformity, there exists x:K. The sequence g^n(a) is a D-pseudo-orbit, (p(g^n(a)),f^n(x.val)) is in V at every n, and there is no b with p(b)=x.val and (g^n(b),g^n(a)) in E at every n. A clopen C contains one whole fibre and avoids another. Its relative image is nonempty, proper and closed, hence not open on connected K. Fix a boundary point and one a in C above it, and set E to the two-cell relation. Each V gives an equicontinuity neighborhood meeting the complement of that image. Every lift of the selected x is outside C and fails at n=0. Compactness of K is unnecessary for this stronger fixed-witness result; compact Y supplies closed images.

**Theorem 1.5 (expansive factor locally constant on).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)] \forall B: Type, [\operatorname{MetricSpace}(B)]\\\forall pi: X \Rightarrow B, \forall f: X \Rightarrow X, \forall d: B \Rightarrow B,\\\operatorname{UniformContinuous}(pi) \land \operatorname{Semiconj}(pi, f, d) \land \operatorname{PositivelyExpansive}(d) \Rightarrow\\\forall K: \operatorname{Set}(X),\\\operatorname{ForwardUniformEquicontinuity}(f, K) \Rightarrow\\\operatorname{IsLocallyConstant}(\operatorname{Restriction}(pi, K))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.expansive_factor_locally_constant_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pull back the positively expansive observation through the explicitly uniformly continuous pi. Equicontinuity makes all projected forward orbits close on a neighborhood of each x:K. Semiconjugacy and positive expansivity identify pi(y) with pi(x) throughout that neighborhood.

**Theorem 1.6 (expansive factor constant on connected).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)] \forall B: Type, [\operatorname{MetricSpace}(B)]\\\forall pi: X \Rightarrow B, \forall f: X \Rightarrow X, \forall d: B \Rightarrow B,\\\operatorname{UniformContinuous}(pi) \land \operatorname{Semiconj}(pi, f, d) \land \operatorname{PositivelyExpansive}(d) \Rightarrow\\\forall K: \operatorname{Set}(X),\\\operatorname{ForwardUniformEquicontinuity}(f, K) \Rightarrow\\\operatorname{IsPreconnected}(K) \Rightarrow\\\operatorname{ConstantOn}(pi, K)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.expansive_factor_constant_on_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ConstantOn(pi,K) is ∀x,y:K, pi(x.val)=pi(y.val). Local constancy and preconnectedness imply this equality. Surjectivity is not required. Consequently positively expansive factors cannot separate a nondegenerate connected equicontinuous subset.

**Theorem 1.7 (contraction pseudo orbit estimate).**

$$\begin{aligned}\forall X: Type, [\operatorname{MetricSpace}(X)]\\\forall f: X \Rightarrow X, \forall q: \mathbb{R},\\0\le q \land q<1 \Rightarrow\\\operatorname{ContractionBound}(f, q) \Rightarrow\\\forall delta: \mathbb{R},\\0\le delta \Rightarrow\\\forall a: \mathbb{N} \Rightarrow X,\\\operatorname{WeakMetricPseudoOrbit}(f, delta, a) \Rightarrow\\\forall n: \mathbb{N},\\\operatorname{GeometricErrorBound}(f, q, delta, a, n)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.contraction_pseudo_orbit_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ContractionBound is ∀x,y, dist(f(x),f(y))≤q dist(x,y). WeakMetricPseudoOrbit is ∀n, dist(f(a(n)),a(n+1))≤delta. The exact GeometricErrorBound is the conjunction dist(f^n(a(0)),a(n))≤delta times the sum of q^j for j<n, and that finite sum times delta≤delta/(1-q). The recurrence e(0)=0 and e(n+1)≤q e(n)+delta proves the first inequality. The geometric-sum identity proves the second. At q=0 and n≥1 the intermediate quantities can be equal; both displayed intermediate comparisons are weak.

**Theorem 1.8 (contraction hasShadowing).**

$$\begin{aligned}\forall X: Type, [\operatorname{MetricSpace}(X)]\\\forall f: X \Rightarrow X, \forall q: \mathbb{R},\\0\le q \land q<1 \Rightarrow\\\operatorname{ContractionBound}(f, q) \Rightarrow\\\operatorname{CompactSpace}(X) \Rightarrow\\\operatorname{HasShadowing}(f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.contraction_hasShadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a metric entourage choose epsilon>0, then delta=(1-q)epsilon/2. The initial point a(0) traces the pseudo-orbit. The preceding weak geometric bounds are followed by the strict comparison delta/(1-q)<epsilon. The cover/uniform equivalence supplies the actual finite-open-cover property, including q=0 and n=0.

**Theorem 1.9 (connected contraction shadowing obstruction).**

$$\begin{aligned}\forall X: Type, [\operatorname{MetricSpace}(X)]\\\forall f: X \Rightarrow X, \forall q: \mathbb{R},\\0\le q \land q<1 \Rightarrow\\\operatorname{ContractionBound}(f, q) \Rightarrow\\\operatorname{CompactSpace}(X) \land \operatorname{PreconnectedSpace}(X) \Rightarrow\\\operatorname{Nondegenerate}(X) \Rightarrow\\\forall Y: Type, [\operatorname{UniformSpace}(Y)] [\operatorname{CompactSpace}(Y)] [\operatorname{TTwoSpace}(Y)] [\operatorname{TotallyDisconnectedSpace}(Y)]\\\forall p: Y \Rightarrow X, \forall g: Y \Rightarrow Y,\\\operatorname{Continuous}(p) \land \operatorname{Surjective}(p) \land \operatorname{Semiconj}(p, g, f) \Rightarrow\\\operatorname{HasShadowing}(f) \land \neg \operatorname{SourceRelativeTracing}(p, g, f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.connected_contraction_shadowing_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All iterates of a q-contraction with 0≤q<1 are nonexpansive, hence uniformly equicontinuous. Use K=X in the connected-subset obstruction. This proves shadowing of the compact metric source and failure of SR for every supplied continuous onto equivariant map from a compact Hausdorff zero-dimensional space. It does not disprove Peng Q5.1, nor assert that any such extension exists or fails ordinary shadowing. The paper's metric extension existence remains an ordinary supplier, not an automatically installed Lean instance. No originality or worldwide resolution claim is made.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.connected_contraction_shadowing_obstruction`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.connected_fixed_orbit_obstruction`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.connected_subset_not_source_relative`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.contraction_hasShadowing`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.contraction_pseudo_orbit_estimate`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.expansive_factor_constant_on_connected`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.expansive_factor_locally_constant_on`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.orbit_lifting_clopen_basis`
- Truth anchor: `D5/S1/Dynamics/Shadowing/EquicontinuousObstruction.orbit_lifting_clopen_image`
- Dependency: [D5/S1/Dynamics/Shadowing/UniformTracing](UniformTracing.md)
