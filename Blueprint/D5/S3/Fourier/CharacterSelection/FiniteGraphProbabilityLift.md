# Finite Graph Probability Lifts

## Abstract

Finite graph vertex laws are classified by positive-fiber anchor laws, with a unique flip-invariant lift.

**Definition 1.1 (Differential and component anchors).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi`

*Formalization.* `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite simple graph, choose one root in every connected component. The map Phi sends a vertex bit configuration to its realizable edge label and its component-root anchor vector. PMF is the finite discrete probability representation used below; its support is exactly the positive point masses.

**Theorem 1.2 (Every realizable label has one lift per anchor).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Phi is a bijection for every finite simple graph, including the empty graph, disconnected graphs, and isolated vertices. The finite cycle-space fiber bijection supplies the unique lift for each realizable label and anchor.

**Definition 1.3 (Component flip action).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip`

*Formalization.* `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A component bit vector acts by adding its bit on every vertex in that component. It fixes the edge differential, translates the anchor vector, and therefore acts on each Phi fiber by anchor translation.

**Theorem 1.4 (Flips preserve edge labels).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip_edgeLabel`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip_edgeLabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The edge label of a flipped configuration is unchanged because adjacent vertices lie in the same connected component and the added bit occurs twice.

**Theorem 1.5 (Flips translate roots).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip_rootAnchors`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip_rootAnchors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each chosen component root, the anchor changes by the corresponding component bit.

**Theorem 1.6 (Positive-fiber conditional classification).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi_probability_lift_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi_probability_lift_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a PMF nu on the realizable labels. Vertex PMFs with differential marginal nu are in bijection with conditional PMFs q_y on anchors indexed only by y in nu.support. The inverse lift samples y from nu, samples its q_y anchor, and applies the inverse of Phi; both inverse laws are part of this equivalence. Zero-mass labels receive no arbitrary kernel.

**Theorem 1.7 (Point masses and zero-mass fibers).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.probability_lift_point_masses`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.probability_lift_point_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For y in nu.support and anchor a, the point mass of the unique lifted configuration Phi inverse (y,a) is nu(y) times q_y(a). For y outside the support every configuration in that fiber has point mass zero.

**Definition 1.8 (The uniform conditional lift).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.uniformLift`

*Formalization.* `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.uniformLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical lift uses PMF.uniformOfFintype on the finite anchor space at every positive label. This is a faithful finite discrete probability measure: every anchor has mass the reciprocal of the anchor-space cardinality.

**Theorem 1.9 (Uniform lift is invariant under every component flip).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.uniform_lift_flip_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.uniform_lift_flip_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform anchor PMF is translation invariant, so the canonical lift is fixed by all component flips.

**Theorem 1.10 (Exactly one flip-invariant lift).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_lift_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_lift_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Among all vertex PMFs with marginal nu, exactly one is invariant under all component flips. Its conditional anchor law on every positive-mass label is uniform. The exact point masses and independent fair component bits are established by flip_invariant_positive_fiber_fair_bits below.

**Theorem 1.11 (Uniformity on every positive fiber).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_positive_fiber_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_positive_fiber_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any flip-invariant lift and any positive label y, the extracted conditional anchor PMF equals PMF.uniformOfFintype on the full anchor space.

**Theorem 1.12 (Conditional independence and fairness of component bits).**

Lean statement: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_positive_fiber_fair_bits`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_positive_fiber_fair_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any flip-invariant lift and any positive label y, fix a finite set S of connected components and prescribe one bit on each component in S. The conditional cylinder probability is exactly (1/2) raised to |S|: Lean expresses this as the point mass of the conditional anchor PMF mapped by restriction to S. The proof identifies its extensions with the freely chosen bits on the complement of S and counts them. Taking S to be a singleton gives probability 1/2 for either bit, and the cylinder formula is the product of these probabilities, establishing mutual conditional independence. The same theorem gives each complete anchor vector mass (1/2) raised to c(G). The empty cylinder has probability one; for the empty graph c(G) is zero and the unique empty anchor vector has mass one.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip_edgeLabel`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.componentFlip_rootAnchors`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_lift_unique`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_positive_fiber_fair_bits`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.flip_invariant_positive_fiber_uniform`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi_bijective`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.phi_probability_lift_classification`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.probability_lift_point_masses`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.uniformLift`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift.uniform_lift_flip_invariant`
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](SimpleGraphCycleSpace.md)
