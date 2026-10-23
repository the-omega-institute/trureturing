# Uniform Shadowing and Prescribed Sources

## Abstract

Finite-cover and uniform shadowing agree on compact uniform spaces; positive expansivity supplies exact-fibre relative tracing.

**Theorem 1.1 (The actual cover contract).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)] [\operatorname{CompactSpace}(X)],\\\forall f: X \Rightarrow X,\\\operatorname{HasShadowing}(f) \iff \operatorname{UniformHasShadowing}(f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/UniformTracing.cover_shadowing_iff_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite open cover C, coverPairs(C) relates two points lying in a single member. The Lebesgue-number lemma makes this an entourage. Conversely, a symmetric square root H of an entourage E gives open neighborhoods inside H-balls; compactness selects a finite cover whose pair relation is contained in E. These two constructions translate all quantifiers of the current HasShadowing interface. Empty spaces and arbitrary self-maps are allowed.

**Theorem 1.2 (SR is exactly OL plus upstairs shadowing).**

$$\begin{aligned}\forall X: Type, [\operatorname{UniformSpace}(X)], \forall Y: Type, [\operatorname{UniformSpace}(Y)],\\\forall p: Y \Rightarrow X, \forall g: Y \Rightarrow Y, \forall f: X \Rightarrow X,\\\operatorname{UniformContinuous}(p) \Rightarrow\\\operatorname{UniformHasShadowing}(g) \Rightarrow\\\operatorname{SourceRelativeTracing}(p, g, f) \iff \operatorname{OrbitLifting}(p, g, f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/UniformTracing.source_relative_iff_orbit_lifting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SR means: for each upstairs entourage E choose D upstairs and V downstairs, before every sequence a and every prescribed x. A D-pseudo-orbit with (p(a(n)), f^n(x)) in V must have a tracer b with p(b)=x and (g^n(b),a(n)) in E at all n. OL replaces the pseudo-orbit by the exact orbit of an arbitrary a, and chooses V before a,x. SR implies OL since exact orbit errors are diagonal. For the reverse implication choose H with H composed with H contained in E, the OL observation, its uniform square root, and a smaller upstairs observation whose p-image is inside that square root. Shadow upstairs first, then lift the already prescribed x by OL and compose the two observations. No semiconjugacy or surjectivity is required for this equivalence; uniform continuity is an explicit premise.

**Theorem 1.3 (Deriving prescribed-source tracing).**

$$\begin{aligned}\forall X: Type, [\operatorname{MetricSpace}(X)], \forall Y: Type, [\operatorname{UniformSpace}(Y)],\\{}[\operatorname{CompactSpace}(Y)],\\\forall p: Y \Rightarrow X, \forall g: Y \Rightarrow Y, \forall f: X \Rightarrow X,\\\operatorname{Continuous}(p) \Rightarrow\\\operatorname{Semiconj}(p, g, f) \Rightarrow\\\operatorname{HasShadowing}(g) \Rightarrow\\\operatorname{PositivelyExpansive}(f) \Rightarrow\\\operatorname{SourceRelativeTracing}(p, g, f)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/UniformTracing.positive_expansivity_source_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive expansivity supplies c>0 such that forward c-close orbits agree, with n=0 included. Use the downstairs distance<c entourage for OL. Equivariance identifies the projected orbit, expansivity forces p(a)=x, and b=a is an OL tracer. Compactness and continuity make p uniformly continuous; the two preceding suppliers now prove SR from actual upstairs shadowing. Neither zero-dimensionality nor surjectivity nor onto dynamics is assumed. This theorem proves SR; it does not replace it by ALP or assert that Peng's unrestricted factors are expansive.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/UniformTracing.cover_shadowing_iff_uniform`
- Truth anchor: `D5/S1/Dynamics/Shadowing/UniformTracing.positive_expansivity_source_relative`
- Truth anchor: `D5/S1/Dynamics/Shadowing/UniformTracing.source_relative_iff_orbit_lifting`
- Dependency: [D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit](MittagLefflerInverseLimit.md)
