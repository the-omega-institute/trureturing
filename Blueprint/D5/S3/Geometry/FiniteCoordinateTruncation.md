# Finite coordinate truncation

## Abstract

Finite-coordinate support, truncation and homotopies in actual independence realizations.

**Definition 1.1 (Probability coordinates).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.Probability`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.Probability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type V, Probability(x) means that all real coordinates x(a) are nonnegative and their sum over V is one.

**Definition 1.2 (Independent coordinate support).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.Avoid`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.Avoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every simple graph G and real coordinate vector x, Avoid(G,x) says that each G-edge has an endpoint with coordinate zero.

**Definition 1.3 (The nonzero support).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.support`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite support of a coordinate vector consists of precisely its nonzero coordinates.

**Theorem 1.4 (Nonempty probability support).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.support_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.support_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative vector whose finite coordinate sum is one has nonempty support.

**Theorem 1.5 (Support independence).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.independent_support_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.independent_support_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite simple graph G and vector x, its nonzero support is independent exactly when every edge has a zero endpoint. No probability assumption is needed.

**Theorem 1.6 (Actual independence realization).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.realization_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.realization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite simple graph G and vector x, membership in the existing coordinate realization of its actual independence complex is equivalent to Probability(x) and Avoid(G,x). The forward direction uses a face containing x; the reverse direction uses the finite nonzero support of x.

**Definition 1.7 (The native topological space).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.Ispace`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.Ispace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ispace(G) is the subtype of finite real coordinate space consisting of the actual realization of the nonempty independent faces of G. Its topology is the inherited subspace topology.

**Definition 1.8 (A coordinate vertex).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.vertex`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each vertex a of G, the vector with coordinate one at a and zero elsewhere belongs to Ispace(G).

**Definition 1.9 (Straight coordinate interpolation).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.mix`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.mix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t and vectors x,y, mix(t,x,y)(a)=(1-t)x(a)+ty(a). At t=0 and t=1 it is x and y respectively.

**Theorem 1.10 (Probability along a segment).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.probability_mix`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.probability_mix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of probability coordinate vectors and every t in the closed unit interval, their straight interpolation is again a probability vector.

**Theorem 1.11 (A segment with shrinking support).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.avoid_mix_of_support`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.avoid_mix_of_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x avoids the edges of G and every zero coordinate of x is also zero in y, then every real straight interpolation of x and y avoids the edges of G.

**Theorem 1.12 (Compatible segments).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.avoid_mix`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.avoid_mix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose that for each G-edge at least one endpoint is zero in both x and y. Every real straight interpolation of x and y then avoids that edge.

**Definition 1.13 (Coordinate normalization).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.normalize`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.normalize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normalize a vector by dividing every coordinate by its finite coordinate sum.

**Theorem 1.14 (Positive normalization).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.probability_normalize`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.probability_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative coordinate vector with strictly positive sum normalizes to a probability vector. A zero coordinate remains zero.

**Definition 1.15 (Coordinate cutoff).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.cut`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real threshold e, cut(e,x)(a)=max(x(a)-e,0). For e nonnegative it preserves every zero coordinate; it kills every coordinate at most e.

**Theorem 1.16 (Total mass after cutoff).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.cut_sum_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.cut_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability vector x and every real e, the sum of cut(e,x) is at least 1-card(V)e. This estimate controls the strict normalization denominators in the star-gadget neighborhoods.

**Theorem 1.17 (Continuity of normalization).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_normalize`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every topological parameter space, a continuous family of finite coordinate vectors has continuous normalization when its coordinate sum never vanishes.

**Theorem 1.18 (Continuity of variable cutoff).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous finite-coordinate family and a continuous real threshold give a continuous cutoff family. This uses coordinatewise maxima of continuous real functions.

**Theorem 1.19 (Joint continuity of interpolation).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_mix`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_mix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every topological parameter space and two continuous finite-coordinate families, straight interpolation is jointly continuous on the unit interval times that space.

**Definition 1.20 (A straight homotopy in a subspace).**

Lean statement: `D5/S3/Geometry/FiniteCoordinateTruncation.straight`

*Formalization.* `D5/S3/Geometry/FiniteCoordinateTruncation.straight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given continuous maps f,g into a specified coordinate subspace D and proofs that every straight interpolation remains in D, straight constructs their actual continuous homotopy. Membership, rather than a homotopy or retraction property, is its hypothesis.

## References

- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.Avoid`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.Ispace`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.Probability`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.avoid_mix`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.avoid_mix_of_support`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_cut`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_mix`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.continuous_normalize`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.cut`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.cut_sum_bound`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.independent_support_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.mix`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.normalize`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.probability_mix`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.probability_normalize`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.realization_iff`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.straight`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.support`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.support_nonempty`
- Truth anchor: `D5/S3/Geometry/FiniteCoordinateTruncation.vertex`
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](FiniteGraphVertexSubstitution.md)
