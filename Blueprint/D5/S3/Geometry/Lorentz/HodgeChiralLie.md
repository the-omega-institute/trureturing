# Lorentz Lie algebra and chiral Hodge decomposition

## Abstract

The real Lorentz matrix Lie algebra has a Pauli realization and its complexification splits into Hodge eigenspaces.

The metric has signature (−,+,+,+). The oriented pair order is (01,02,03,23,31,12). The same Lorentz signature fixes the null directions used in local horizon geometry. Index lowering identifies Lorentz endomorphisms with covariant two-forms.

**Definition 1.1 (The Lorentz metric).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.eta`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.eta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal entries of the four-by-four metric are minus one followed by three ones.

**Definition 1.2 (Lorentz matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentzLie`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentzLie` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the Lie subalgebra of skew-adjoint endomorphisms for the indicated Lorentz metric.

**Definition 1.3 (Rotation and boost coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentzCoords`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentzCoords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rotation coordinates are (−X₂₃,−X₃₁,−X₁₂) and the boost coordinates are (X₀₁,X₀₂,X₀₃). The skew-adjoint equation forces every diagonal entry to vanish, every time-space pair to agree and every spatial pair to have opposite signs. The inverse puts the rotation and boost coordinates into precisely those entries. Both maps are linear.

**Definition 1.4 (Oriented cross product).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.cross`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.cross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For triples a and b, the entries are a₁b₂−a₂b₁, a₂b₀−a₀b₂ and a₀b₁−a₁b₀ in zero-based indices.

**Theorem 1.5 (Lorentz bracket in six coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_coords_bracket`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_coords_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rotation and boost triples (a,b) and (c,d), ordinary matrix commutation has coordinates (a×c−b×d, a×d+b×c). Multiplication of the explicit four-by-four matrices proves each component.

**Theorem 1.6 (Real dimension six).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.finrank_lorentz_real`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.finrank_lorentz_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate linear equivalence identifies the real carrier with a product of two three-dimensional spaces.

**Definition 1.7 (Complex special linear Lie algebra).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.SL2C`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.SL2C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The special linear carrier consists of traceless complex two-by-two matrices.

**Definition 1.8 (Normalized Pauli map).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauli`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauli` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of z has diagonal entries −iz₂/2 and iz₂/2 and off-diagonal entries (−iz₀−z₁)/2 and (−iz₀+z₁)/2.

**Definition 1.9 (Pauli linear equivalence).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauliCoords`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauliCoords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a traceless matrix M, the inverse triple is (i(M₀₁+M₁₀), M₁₀−M₀₁, 2iM₀₀). The trace condition recovers the remaining diagonal entry and i²=−1 proves both compositions.

**Theorem 1.10 (The Pauli commutator).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauli_bracket`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauli_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutator of the Pauli images of two triples is the Pauli image of their cross product. Expanding the four entries and reducing i²=−1 proves the identity.

**Definition 1.11 (Real Lie equivalence).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_real_sl2`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_real_sl2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-linear map takes (a,b) to the Pauli image of a−ib in the real restriction of scalars of the complex special linear algebra. The coordinate inverse uses real part and negative imaginary part. The Lorentz bracket becomes the Pauli commutator because the complex cross product of a−ib and c−id equals (a×c−b×d)−i(a×d+b×c).

**Definition 1.12 (Two complex Lie factors).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_chiral_sl2_prod`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_chiral_sl2_prod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Send (a,b) to the two Pauli images of a−ib and a+ib. For their coordinate triples u and v the inverse is a=(u+v)/2 and b=−i(v−u)/2. Expanding both cross products verifies preservation of the Lie bracket.

**Definition 1.13 (Complexification of real matrices).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_base_change`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_base_change` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tensor extension over the real numbers gives the complex matrix algebra. A pure tensor z⊗X has coordinates z times the real coordinates of X. The tensor equivalences distributing over the coordinate product and its three scalar entries supply the linear inverse. The coordinate bracket table proves compatibility on pure tensors, and additivity extends it to all tensors.

**Definition 1.14 (Complexified chiral Lie equivalence).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.complexified_chiral_sl2_prod`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.complexified_chiral_sl2_prod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composing the extension-of-scalars equivalence with the two-factor Pauli equivalence identifies the complexification with the product of two complex special linear Lie algebras.

**Definition 1.15 (Rotation generators).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.J`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rotation generator has its coordinate unit vector in the rotation triple and zero boost triple.

**Definition 1.16 (Boost generators).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.K`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The boost generator has zero rotation triple and its coordinate unit vector in the boost triple.

**Definition 1.17 (First chiral generator).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralPlus`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first combination of the generators is (J+iK)/2.

**Definition 1.18 (Second chiral generator).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralMinus`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second combination of the generators is (J−iK)/2.

**Theorem 1.19 (Images of the chiral generators).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_generator_images`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_generator_images` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each first chiral generator maps to its Pauli basis element in the first factor and zero in the second. Each second chiral generator gives zero in the first factor and its Pauli basis element in the second.

**Theorem 1.20 (Mixed brackets vanish).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_mixed_bracket`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_mixed_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

First and second chiral generators lie in different factors. Their product-Lie commutator vanishes componentwise and the Lie equivalence is injective.

**Theorem 1.21 (The chiral commutator table).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_brackets`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_brackets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Within either factor, the commutator is the Pauli image of the cross product of the two coordinate unit vectors. These cross products give the oriented antisymmetric structure constants. The mixed commutator is zero.

**Theorem 1.22 (Lorentzian Hodge operator).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_hodge_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_hodge_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

The second exterior power of the metric is diagonal with minus one in the electric block and plus one in the magnetic block. It is its own inverse. The Urbantke wedge pairing exchanges the two blocks, so the volume-one Hodge matrix takes (E,B) to (B,−E).

**Theorem 1.23 (Real Hodge square).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.real_hodge_square`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.real_hodge_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Applying the signed block matrix twice negates each two-form coefficient.

**Definition 1.24 (The covariant two-form).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_to_twoForm`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_to_twoForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the Lorentz endomorphism by the metric on the left and extract entries in the oriented pair order.

**Theorem 1.25 (Two-form coordinates of the Lorentz generator).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.twoForm_coords`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.twoForm_coords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lowered time-space entries are the negatives of the boost coordinates. The cyclic spatial entries are the negatives of the rotation coordinates. The resulting pair is (−b,−a).

**Theorem 1.26 (Hodge eigenspaces and the two Lie factors).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.hodge_eigenspaces_eq_chiral`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.hodge_eigenspaces_eq_chiral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Under index lowering, a Lorentz matrix has Hodge eigenvalue −i exactly when its second Pauli factor vanishes. Eigenvalue +i similarly characterizes vanishing of the first factor. The electric block equation determines the rotation triple in terms of the boost triple, and the magnetic equation follows from i²=−1.

**Definition 1.27 (Three-column chiral graph).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralGraph`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The electric block is the identity matrix and the magnetic block is z times the identity.

**Theorem 1.28 (Graph of a Hodge eigenvalue).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.hodge_eigen_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.hodge_eigen_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z²=−1 a vector is a z eigenvector exactly when its magnetic triple is z times its electric triple. Each electric triple determines one such vector and the second block equation follows from z²=−1.

**Theorem 1.29 (Wedge Gram matrix of the graph).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_graph_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_graph_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

The two complementary blocks each contribute z times the identity to the wedge Gram matrix, yielding 2z times the identity.

**Theorem 1.30 (Conjugation exchanges the graphs).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_graph_conj`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_graph_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entrywise conjugation fixes the identity electric block and takes i to −i in the magnetic block.

**Theorem 1.31 (Urbantke Lorentzian normalization).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.urbantke_chiral_graph`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.urbantke_chiral_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

For the graph with magnetic block iI, the frozen cubic metric is minus the chosen Lorentz metric and its volume coefficient is −i. This is the graph carrying eigenvalue +i of the real volume-one Hodge matrix.

**Definition 1.32 (Bivector of the null screen).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.screenWedge`

*Formalization.* `D5/S3/Geometry/Lorentz/HodgeChiralLie.screenWedge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw wedge entries use the complex screen vector followed by the real null generator in the oriented pair order.

**Theorem 1.33 (Null screen bivector in a Hodge plane).**

Lean statement: `D5/S3/Geometry/Lorentz/HodgeChiralLie.weyl_screen_in_chiral_plane`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/HodgeChiralLie.weyl_screen_in_chiral_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

In both stereographic charts the raw magnetic triple is −i times the electric triple. The signed Hodge matrix thus has eigenvalue −i on the screen wedge. Lowering two contravariant indices reverses the electric signs and exchanges the graph.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.J`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.K`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.SL2C`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralGraph`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralMinus`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiralPlus`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_brackets`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_generator_images`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_graph_conj`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_graph_gram`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.chiral_mixed_bracket`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.complexified_chiral_sl2_prod`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.cross`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.eta`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.finrank_lorentz_real`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.hodge_eigen_graph`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.hodge_eigenspaces_eq_chiral`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentzCoords`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentzLie`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_base_change`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_chiral_sl2_prod`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_coords_bracket`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_hodge_blocks`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_real_sl2`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.lorentz_to_twoForm`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauli`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauliCoords`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.pauli_bracket`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.real_hodge_square`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.screenWedge`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.twoForm_coords`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.urbantke_chiral_graph`
- Truth anchor: `D5/S3/Geometry/Lorentz/HodgeChiralLie.weyl_screen_in_chiral_plane`
- Dependency: [D5/S3/Geometry/Lorentz/Urbantke](Urbantke.md)
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
