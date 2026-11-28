# Exceptional roots and trinification

## Abstract

The exceptional root system, chiral weight traces, and invariant matrix cubic.

The root coordinates use an integral code scaled by one half. The chiral basis combines the even half-spin weights, the fundamental vector weights and their duals, and a neutral state. Right indices zero, one, and two label the up antiquark, down antiquark, and exotic antiquark in the conjugate quark block. Those indices label the up doublet, down doublet, and lepton doublet in the corresponding columns of the lepton block.

**Theorem 1.1 (Chiral multiplet dimension).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.state_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.state_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Slansky (1981). *Group Theory for Unified Model Building*. DOI: [10.1016/0370-1573(81)90092-2](https://doi.org/10.1016/0370-1573(81)90092-2).

*Commentary.*

The chiral state type has sixteen spinor states, two sets of five vector states, and one singlet, for a total of twenty-seven. Every state has psi charge one, minus two, or four.

**Theorem 1.2 (One Standard Model family and a neutral state).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.spinor_sm_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.spinor_sm_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Slansky (1981). *Group Theory for Unified Model Building*. DOI: [10.1016/0370-1573(81)90092-2](https://doi.org/10.1016/0370-1573(81)90092-2).

*Commentary.*

The spinor block contains the fifteen Standard Model weights, compared with the preceding gauge unification module, and one hypercharge and isospin neutral state.

**Theorem 1.3 (Spinor charges from occupation coordinates).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.spinor_occupation_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.spinor_occupation_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The half-spin occupation coordinates recover the hypercharge, isospin, electric charge, and baryon-minus-lepton charge of each spinor state.

**Theorem 1.4 (Vanishing linear traces).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.linear_traces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.linear_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hypercharge, weak isospin, electric charge, the two extra abelian charges, and baryon-minus-lepton charge each have sum zero over the twenty-seven states.

**Theorem 1.5 (Complete quadratic trace pairing).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trace_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trace_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of the product of arbitrary linear combinations of hypercharge, weak isospin, and the two additional charges is the diagonal bilinear form with coefficients five, three, seventy-two, and one hundred twenty.

**Theorem 1.6 (Orthogonal diagonal generators).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.pairwise_orthogonality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.pairwise_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All six mixed traces between hypercharge, weak isospin, and the two extra abelian charges vanish.

**Theorem 1.7 (Exact quadratic indices).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.quadratic_traces`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.quadratic_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weak-isospin, hypercharge, electric-charge, psi-charge, and chi-charge square sums are respectively three, five, eight, seventy-two, and one hundred twenty.

**Theorem 1.8 (Tree-level weak mixing ratio).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.weinberg_trace_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.weinberg_trace_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio of the weak-isospin square trace to the electric-charge square trace is three eighths.

**Theorem 1.9 (Cubic anomaly polynomial).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.universal_abelian_cubic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.universal_abelian_cubic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of cubes of any real linear combination of hypercharge, weak isospin, psi charge, and chi charge vanishes.

**Theorem 1.10 (Mixed cubic traces).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.mixed_abelian_cubic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.mixed_abelian_cubic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the pointwise product of three independently chosen real linear combinations of the four generators vanishes.

**Theorem 1.11 (Color multiplet counts).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.color_content`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.color_content` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chiral basis has nine triplet components, nine antitriplet components, and nine singlets. The colored components form three triplet and three antitriplet multiplets.

**Theorem 1.12 (Pure color and mixed color anomalies).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.color_anomalies`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.color_anomalies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed cubic color trace vanishes. The color-index-weighted sum of any real linear combination of the four abelian weights also vanishes.

**Theorem 1.13 (Electric and electroweak weight identification).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit coordinate equivalence preserves hypercharge, weak isospin, and electric charge state by state.

**Theorem 1.14 (Additional trinification charges).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_extra_charges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_extra_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate equivalence preserves the psi and chi charges and their baryon-minus-lepton combination with hypercharge.

**Theorem 1.15 (Color-preserving coordinate equivalence).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_color`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_color` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence preserves each state’s color sector and its color index when the state has one.

**Theorem 1.16 (Seventy-two exceptional roots).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral sign-code construction gives forty integral roots and thirty-two half-integral roots, and its realization is injective.

**Theorem 1.17 (Exceptional root subspace).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_in_rank6_subspace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_in_rank6_subspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sixth and seventh coordinates agree and are negatives of the eighth. The subspace of vectors with these two constraints has dimension six.

**Theorem 1.18 (Root-space dimension count).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_lie_algebra_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_lie_algebra_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six Cartan dimensions and the seventy-two root positions give a count of seventy-eight.

**Theorem 1.19 (Common squared root length).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_simply_laced`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_simply_laced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vector in the exceptional root set has squared Euclidean length two.

**Theorem 1.20 (Integral root pairings).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_crystallographic_inner_products`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_crystallographic_inner_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two roots have inner product in the five integers from minus two through two. The extreme values distinguish opposite and equal roots, respectively.

**Theorem 1.21 (Weyl reflection and negation).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_weyl_reflection_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_weyl_reflection_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the inner product times the reflecting root from a second root gives another root. Negating a root gives a root as well.

**Theorem 1.22 (Exceptional simple system and Cartan determinant).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_dynkin_simple_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_dynkin_simple_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six displayed roots are linearly independent and give the Bourbaki Cartan matrix of determinant three. Each root expands in their basis with integral coefficients of one weak sign.

**Theorem 1.23 (Full rank of the root span).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_root_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_root_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The root span equals the six-dimensional subspace described by the two coordinate equations.

**Theorem 1.24 (Trace-free electroweak diagonals).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_diagonal_generators`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_diagonal_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left and right hypercharge diagonals and weak-isospin diagonal have zero trace. Subtracting the isospin diagonal from the left hypercharge diagonal gives the right hypercharge diagonal.

**Theorem 1.25 (Matrix-space dimension).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three complex three by three matrix blocks have total complex dimension twenty-seven. Two triples coincide exactly when their entries agree at every index of the chiral basis.

**Theorem 1.26 (Cyclic symmetry of the group action).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cyclic_equivariance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cyclic_equivariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cycling the three matrices intertwines the rotation of the three determinant-one factors. Three rotations act as the identity.

**Theorem 1.27 (Diagonal cube-root kernel).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_action_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_action_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A group element acts trivially on all three matrices exactly when its three factors are the same scalar matrix and that scalar has cube one.

**Theorem 1.28 (Arbitrary trinification Cartan anomaly).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cartan_cubic_anomaly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cartan_cubic_anomaly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any three trace-free diagonals, the sum of cubes of the cyclic differences over all matrix entries vanishes.

**Theorem 1.29 (Determinant-one change of bases).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_sl3_cubed_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_sl3_cubed_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three determinants and the trace of the triple product give an invariant of determinant-one changes of basis on the three matrix spaces.

**Theorem 1.30 (Cyclic invariance of the cubic).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_z3_cyclic_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_z3_cyclic_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cyclic permutation of the three matrix arguments preserves the sum of determinants minus the trace of their product.

**Theorem 1.31 (Degree-three homogeneity).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_homogeneous_degree_3`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_homogeneous_degree_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scaling all three matrices by a complex scalar multiplies the invariant by the cube of the scalar.

**Theorem 1.32 (Cubic-preserving linear action and cyclic element).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cubic_stabilizer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cubic_stabilizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant-one factors act by linear automorphisms in the cubic stabilizer. The cyclic element has exact order three and conjugates the action by rotation of the three factors.

**Theorem 1.33 (Quark and lepton Yukawa coefficients).**

Lean statement: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_contains_sm_yukawa`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_contains_sm_yukawa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two weak rows in the trace terms at right indices zero and one supply the up and down quark couplings. The determinant uses the three distinct right indices and the alternating contraction of the two weak rows. Its expansions at the charged and neutral singlets give the charged-lepton and Dirac-neutrino couplings.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.color_anomalies`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.color_content`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_card`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_crystallographic_inner_products`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_in_rank6_subspace`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_simply_laced`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6Roots_weyl_reflection_closed`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_dynkin_simple_roots`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_lie_algebra_dimension`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.e6_root_span`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_contains_sm_yukawa`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_homogeneous_degree_3`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_sl3_cubed_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.freudenthalCubic_z3_cyclic_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.linear_traces`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.mixed_abelian_cubic`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.pairwise_orthogonality`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.quadratic_traces`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.spinor_occupation_bridge`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.spinor_sm_bridge`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.state_card`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trace_pairing`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_action_kernel`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cartan_cubic_anomaly`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cubic_stabilizer`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_cyclic_equivariance`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinif_dimension`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_color`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_diagonal_generators`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_extra_charges`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.trinification_weights`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.universal_abelian_cubic`
- Truth anchor: `D5/S3/Quantum/Gauge/E6TrinificationUnification4D.weinberg_trace_ratio`
- Dependency: [D5/S3/Quantum/Gauge/GaugeUnificationRG4D](GaugeUnificationRG4D.md)
- Dependency: [D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D](SU5SO10GrandUnification4D.md)
