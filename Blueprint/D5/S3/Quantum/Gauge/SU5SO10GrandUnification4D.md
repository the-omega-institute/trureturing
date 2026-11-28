# Special unitary and orthogonal unification

## Abstract

Unified gauge generators, adjoint and fermion weights, and chiral spinor charges.

The fundamental coordinates consist of a color triple and a weak pair. The Hermitian convention gives the hypercharge weights minus one third on color and one half on the weak pair. Matrix commutators measure differences of weights, while the second exterior power adds the weights of its two factors.

**Definition 1.1 (Embedded gauge generators).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.smEmbedding`

*Formalization.* `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.smEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

The color and weak matrices occupy disjoint diagonal blocks. The remaining summand is the normalized hypercharge matrix multiplied by an arbitrary real coefficient.

**Theorem 1.2 (Traceless Hermitian embedding).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_embedding_traceless_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_embedding_traceless_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

For traceless Hermitian color and weak inputs and any real hypercharge coefficient, their embedded sum has zero trace and is Hermitian.

**Theorem 1.3 (Recovery of the gauge generators).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_sm_embedding_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_sm_embedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal embedded matrices with traceless color inputs have equal color matrices, equal weak matrices, and equal real hypercharge coefficients.

**Theorem 1.4 (Commuting gauge factors).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_sm_blocks_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_sm_blocks_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The color and weak embeddings commute for arbitrary input matrices. Both commute with the hypercharge generator in its normalized and unnormalized forms.

**Theorem 1.5 (Gauge generator normalization).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_trace_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_trace_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

The squared traces of the normalized hypercharge generator, the third weak generator, and the eighth color generator all equal one half. The squared trace of unnormalized hypercharge is five sixths, so its ratio to the weak squared trace is five thirds.

**Theorem 1.6 (Fundamental electric charge).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_electric_charge_traceless`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_electric_charge_traceless` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

The electric charge diagonal contains three copies of minus one third followed by one and zero, and its trace vanishes.

**Theorem 1.7 (Weak mixing angle at unification).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_weinberg_angle_from_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_weinberg_angle_from_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The electric squared trace is four thirds. Dividing the weak squared trace by it gives three eighths.

**Theorem 1.8 (Unique adjoint decomposition).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

Every traceless five by five matrix has unique traceless color and weak components, one hypercharge scalar, and two rectangular components.

**Theorem 1.9 (Adjoint component dimensions).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_dimensions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_dimensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The color and weak traceless spaces have dimensions eight and three. Each rectangular space has dimension six. Together with the hypercharge line the full traceless space has dimension twenty-four.

**Theorem 1.10 (Action on the adjoint components).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_block_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_block_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commutation with a block-diagonal generator gives the color and weak commutators and zero hypercharge scalar. Each rectangle receives left multiplication by its row generator, negative right multiplication by its column generator, and a hypercharge term with coefficient minus or plus five sixths of the generator parameter.

**Theorem 1.11 (Irreducibility of the adjoint components).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_blocks_irreducible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_blocks_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either traceless square block, an invariant subspace contained in the trace-zero space is zero or the whole trace-zero space. For either rectangle, stability under the left and right traceless matrices forces the same alternatives. The hypercharge line is one-dimensional.

**Theorem 1.12 (Adjoint hypercharge weights).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_hypercharge_eigenvalues`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_hypercharge_eigenvalues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

For each matrix unit the hypercharge commutator is the unit multiplied by its row weight minus its column weight. The two diagonal blocks have weight zero, the color to weak block has weight minus five sixths, and the weak to color block has weight plus five sixths.

**Theorem 1.13 (Off-diagonal electric charges).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_leptoquark_electric_charges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_leptoquark_electric_charges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

For each color, the electric charge commutator has eigenvalues minus four thirds and minus one third on the two color to weak units. The reversed units have eigenvalues plus four thirds and plus one third.

**Definition 1.14 (Dual generators).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.dualAction`

*Formalization.* `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.dualAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

The dual infinitesimal action is the negative transpose.

**Definition 1.15 (Second exterior-power generators).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.exteriorAction`

*Formalization.* `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.exteriorAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

The infinitesimal generator acts on both slots of a wedge pair by the exterior product rule.

**Definition 1.16 (Coordinates of an exterior pair).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.wedgeCoords`

*Formalization.* `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.wedgeCoords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each entry is the two by two minor of the pair of vectors at the corresponding ordered indices.

**Theorem 1.17 (Exterior product rule).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_exterior_product_rule`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_exterior_product_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any fundamental matrix and any pair of vectors, the exterior action on their wedge is the sum of the two wedges obtained by acting on one vector at a time.

**Theorem 1.18 (Induced diagonal actions).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_fermion_weight_actions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_fermion_weight_actions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the dual each diagonal entry changes sign. On the second exterior power the diagonal entry of an ordered pair is the sum of the two selected entries.

**Theorem 1.19 (Number of Weyl states).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_bar5_plus_10_dim`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_bar5_plus_10_dim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex space indexed by the five dual coordinates and ten wedge coordinates has dimension fifteen.

**Theorem 1.20 (One-generation charges and traces).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_bar5_plus_10_matches_sm_hypercharges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_bar5_plus_10_matches_sm_hypercharges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The induced hypercharge and third weak weight agree with the Standard Model tables in all fifteen slots. The first and third hypercharge moments vanish, the second is ten thirds, and the two mixed color and weak hypercharge sums vanish.

**Theorem 1.21 (Cubic trace of the exterior square).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.suN_antisym_cubic_anomaly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.suN_antisym_cubic_anomaly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a traceless real Cartan vector in any dimension, the sum of the cubes of the pair weights equals the fundamental cubic trace multiplied by the dimension minus four.

**Theorem 1.22 (Opposite cubic traces).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_cubic_anomaly_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_cubic_anomaly_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi and Sheldon Lee Glashow (1974). *Unity of All Elementary-Particle Forces*. DOI: [10.1103/PhysRevLett.32.438](https://doi.org/10.1103/PhysRevLett.32.438). URL: <https://doi.org/10.1103/PhysRevLett.32.438>.

*Commentary.*

For a real traceless Cartan vector the exterior square contributes the fundamental cubic trace. The dual contributes its negative. Their sum is zero.

**Theorem 1.23 (Baryon minus lepton charge at gauge vertices).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_b_minus_l_conserved`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_b_minus_l_conserved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In either fermion representation, a matrix unit with a nonzero action coefficient carries the outgoing minus incoming baryon minus lepton charge. The adjoint assignment is four fifths of the adjoint hypercharge and equals plus or minus two thirds on the off-diagonal gauge units.

**Definition 1.24 (Real orthogonal action).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5ToSo10`

*Formalization.* `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5ToSo10` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Harald Fritzsch and Peter Minkowski (1975). *Unified interactions of leptons and hadrons*. DOI: [10.1016/0003-4916(75)90211-0](https://doi.org/10.1016/0003-4916(75)90211-0). URL: <https://doi.org/10.1016/0003-4916(75)90211-0>.

*Commentary.*

The special unitary action on five complex coordinates gives a multiplicative special orthogonal action on ten real coordinates by taking real and imaginary blocks.

**Theorem 1.25 (Faithful real orthogonal action).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_to_so10_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_to_so10_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real orthogonal action determines the original special unitary matrix.

The half-spin weight model uses five occupation bits. Even occupations have degrees zero, two, and four with respective counts one, ten, and five. The shift by minus half the trace gives a sum of occupied weights on the traceless Cartan. The degree-four weight equals minus the missing coordinate. The cubic trace of the sixteen even weights vanishes for every real Cartan vector, and the five charge assignments are evaluated in every slot.

**Theorem 1.26 (Traceless Cartan branching).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.so10_su5_fermion_branching`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.so10_su5_fermion_branching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Harald Fritzsch and Peter Minkowski (1975). *Unified interactions of leptons and hadrons*. DOI: [10.1016/0003-4916(75)90211-0](https://doi.org/10.1016/0003-4916(75)90211-0). URL: <https://doi.org/10.1016/0003-4916(75)90211-0>.

*Commentary.*

For every real traceless Cartan vector, the even spinor weights in order equal the neutral singlet followed by the fifteen dual and exterior weights.

**Theorem 1.27 (Spinor baryon minus lepton matching).**

Lean statement: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.so10_su5_b_minus_l_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.so10_su5_b_minus_l_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Harald Fritzsch and Peter Minkowski (1975). *Unified interactions of leptons and hadrons*. DOI: [10.1016/0003-4916(75)90211-0](https://doi.org/10.1016/0003-4916(75)90211-0). URL: <https://doi.org/10.1016/0003-4916(75)90211-0>.

*Commentary.*

The empty occupation has baryon minus lepton charge one. Each other slot has the charge induced from its exterior pair or missing dual coordinate.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.dualAction`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.exteriorAction`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.smEmbedding`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.so10_su5_b_minus_l_compatibility`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.so10_su5_fermion_branching`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5ToSo10`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_block_action`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_blocks_irreducible`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_decomposition`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_dimensions`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_adjoint_hypercharge_eigenvalues`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_b_minus_l_conserved`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_bar5_plus_10_dim`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_bar5_plus_10_matches_sm_hypercharges`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_cubic_anomaly_cancellation`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_electric_charge_traceless`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_embedding_traceless_hermitian`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_exterior_product_rule`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_fermion_weight_actions`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_leptoquark_electric_charges`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_sm_blocks_commute`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_sm_embedding_injective`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_to_so10_injective`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_trace_normalization`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.su5_weinberg_angle_from_trace`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.suN_antisym_cubic_anomaly`
- Truth anchor: `D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D.wedgeCoords`
- Dependency: [D5/S3/Quantum/Gauge/GaugeUnificationRG4D](GaugeUnificationRG4D.md)
