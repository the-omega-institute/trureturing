# Plebański simplicity for triples of two-forms

## Abstract

The algebraic geometry of the four-dimensional chiral simplicity equations.

Use the oriented pair basis (01, 02, 03, 23, 31, 12). The wedge Gram matrix Q is the matrix of wedge pairings relative to the coordinate volume. Simplicity means Q is its mean trace times the identity. The model G(z) has upper block I and lower block zI. A coframe acts by its second exterior power, written act. The five coordinates are Q₀₁, Q₀₂, Q₁₂, Q₀₀ − Q₂₂, and Q₁₁ − Q₂₂. The function signValue takes true to 1 and false to −1. The sector with labels t and s is signValue(t) times G(z signValue(s)). The model metric is diag(1,z²,z²,z²). The function sumsquares adds the squares of the four coordinates.

**Theorem 1.1 (Five simplicity equations).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; (\operatorname{Simple}\left(B\right) \iff \operatorname{five}\left(\operatorname{Q}\left(B\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simple_iff_five_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three off-diagonal entries and two differences of diagonal entries vanish exactly when the symmetric Gram matrix is scalar.

**Theorem 1.2 (Quadratic expansion).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; \forall X \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; \forall t \in K,\; \operatorname{five}\left(\operatorname{Q}\left(B + (t \cdot X)\right)\right) = \operatorname{five}\left(\operatorname{Q}\left(B\right)\right) + (t \cdot \operatorname{Jacobian}\left(B, X\right)) + ((t)^{2} \cdot \operatorname{five}\left(\operatorname{Q}\left(X\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicity_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of the first power of the parameter defines the Jacobian.

**Theorem 1.3 (Surjective Jacobian).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; (\operatorname{LinearIndependent}\left(K, \operatorname{columns}\left(B\right)\right) \implies \operatorname{Surjective}\left(\operatorname{Jacobian}\left(B\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicityDeriv_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full column rank gives a right inverse to the transposed triple. The wedge pairing is an involution. Apply the right inverse and wedge pairing to half of a symmetric lift of the coordinates.

**Theorem 1.4 (Jacobian rank and tangent dimension).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; (\operatorname{LinearIndependent}\left(K, \operatorname{columns}\left(B\right)\right) \implies (\operatorname{dim}\left(\operatorname{range}\left(\operatorname{Jacobian}\left(B\right)\right)\right) = 5 \land \operatorname{dim}\left(\operatorname{ker}\left(\operatorname{Jacobian}\left(B\right)\right)\right) = 13))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicity_jacobian_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five equations have independent derivatives at every triple with independent columns. Rank-nullity in the eighteen-dimensional space of triples gives the dimension of the tangent space at any such solution.

**Theorem 1.5 (Coframe covariance of the Gram matrix).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall A \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; \operatorname{Q}\left(\operatorname{act}\left(A, B\right)\right) = (\operatorname{det}\left(A\right) \cdot \operatorname{Q}\left(B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.wedgeGram_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The wedge pairing scales by the coframe determinant, including when the coframe is singular.

**Theorem 1.6 (Coframe covariance of the cubic).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall A \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; \operatorname{U}\left(\operatorname{act}\left(A, B\right)\right) = (\operatorname{det}\left(A\right) \cdot A \cdot \operatorname{U}\left(B\right) \cdot (A)^{T})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.urbantke_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Write each term of the cubic as a product of two skew matrices and the skew matrix of a complementary bivector. The wedge law contracts the two middle coframe factors. The two free factors act by congruence.

**Theorem 1.7 (Negation of the triple).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; (\operatorname{Q}\left(- B\right) = \operatorname{Q}\left(B\right) \land \operatorname{U}\left(- B\right) = - \operatorname{U}\left(B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicity_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negation preserves the quadratic Gram matrix and reverses the cubic Urbantke density.

**Theorem 1.8 (Two degenerate simplicity witnesses).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] (\operatorname{Q}\left(\operatorname{G}\left(0\right)\right) = 0 \land \operatorname{rank}\left(\operatorname{U}\left(\operatorname{G}\left(0\right)\right)\right) = 1 \land \operatorname{spatial} \ne 0 \land \operatorname{Q}\left(\operatorname{spatial}\right) = 0 \land \operatorname{U}\left(\operatorname{spatial}\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.degenerate_simplicity_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

The upper identity block gives the triple of wedges with a common covector. Its Urbantke matrix has a single nonzero entry. The lower identity block gives the three spatial wedges. In its cubic every term contains a row involving the time index.

**Theorem 1.9 (Characteristic-zero normal form).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; ((\operatorname{Simple}\left(B\right) \land \operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0) \iff \exists A \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \exists z \in K,\; (\operatorname{det}\left(A\right) \ne 0 \land z \ne 0 \land B = \operatorname{act}\left(A, \operatorname{G}\left(z\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.exists_graph_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Nondegeneracy makes the symmetric Urbantke density invertible. A determinant-one shear brings a nonzero value of its quadratic form to the time entry, which is the electric determinant. Normalize the electric block by a spatial coframe. Simplicity then makes the symmetric part of the magnetic block scalar. A second shear supplies its skew part.

**Theorem 1.10 (Four-square orbit criterion).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall z \in K,\; \forall w \in K,\; ((z \ne 0 \land w \ne 0) \implies (\exists A \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; (\operatorname{det}\left(A\right) \ne 0 \land \operatorname{act}\left(A, \operatorname{G}\left(z\right)\right) = \operatorname{G}\left(w\right)) \iff \exists q \in K^{4},\; \operatorname{sumsquares}\left(q\right) = \frac{w}{z}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.model_orbit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Comparing Gram matrices fixes the relative coframe determinant. Comparing the time entry of the cubic expresses that determinant as a sum of four squares. For the converse, quaternion right multiplication scales the unit model by the quaternion norm. Spatial dilations transport this identity to the two models.

**Theorem 1.11 (Oriented Euclidean normal form).**

$$\forall B \in \operatorname{Mat}_{6 \times 3}\left(\mathbb{R}\right),\; ((\operatorname{Simple}\left(B\right) \land \operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0) \iff \exists A \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \exists t \in \operatorname{Bool},\; \exists s \in \operatorname{Bool},\; ((0 < \operatorname{det}\left(A\right)) \land B = \operatorname{act}\left(A, \operatorname{sectorModel}\left(1, t, s\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.euclidean_model_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. De Pietri and L. Freidel (1999). *so(4) Plebanski action and relativistic spin-foam model*. DOI: [10.1088/0264-9381/16/7/303](https://doi.org/10.1088/0264-9381/16/7/303). URL: <https://arxiv.org/abs/gr-qc/9804071>.

*Commentary.*

A positive ratio of scalar graph parameters is a real square. Time reflection reverses coframe orientation and switches the two signs in the model. The overall sign and chirality give four labels for the oriented models.

**Theorem 1.12 (Orbits at a fixed metric).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall f \in \operatorname{RingHom}\left(\mathbb{R}, K\right),\; \forall z \in K,\; \forall j \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \forall g \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \forall A \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \forall C \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \forall t \in \operatorname{Bool},\; \forall s \in \operatorname{Bool},\; \forall v \in \operatorname{Bool},\; \forall w \in \operatorname{Bool},\; ((z \ne 0 \land f\left(j\right) = \operatorname{modelMetric}\left(z\right) \land \operatorname{det}\left(g\right) \ne 0 \land (0 < \operatorname{det}\left(A\right)) \land (0 < \operatorname{det}\left(C\right)) \land A \cdot j \cdot (A)^{T} = g \land C \cdot j \cdot (C)^{T} = g) \implies (\exists L \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; (\operatorname{OrientedIsometry}\left(g, L\right) \land \operatorname{act}\left(f\left(L\right), \operatorname{act}\left(f\left(A\right), \operatorname{sectorModel}\left(z, t, s\right)\right)\right) = \operatorname{act}\left(f\left(C\right), \operatorname{sectorModel}\left(z, v, w\right)\right)) \iff (t = v \land s = w)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.fixed_metric_sector_orbit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. De Pietri and L. Freidel (1999). *so(4) Plebanski action and relativistic spin-foam model*. DOI: [10.1088/0264-9381/16/7/303](https://doi.org/10.1088/0264-9381/16/7/303). URL: <https://arxiv.org/abs/gr-qc/9804071>.

*Commentary.*

For a fixed normalized metric, its two oriented coframes have the same positive determinant. The Gram scalar and cubic density distinguish the chiral and overall labels. The quotient of the two coframes is an oriented real isometry and maps representatives with matching labels.

**Theorem 1.13 (Oriented Lorentzian normal form).**

$$\forall B \in \operatorname{Mat}_{6 \times 3}\left(\mathbb{C}\right),\; (((\operatorname{Simple}\left(B\right) \land \operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0) \land ((B)^{T} \cdot \operatorname{W}\left(\mathbb{C}\right) \cdot \operatorname{conj}\left(B\right) = 0 \land \operatorname{conj}\left(\operatorname{U}\left(B\right)\right) = \operatorname{U}\left(B\right) \land \operatorname{Re}\left(\operatorname{gramScalar}\left(B\right)\right) = 0)) \iff \exists A \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \exists t \in \operatorname{Bool},\; \exists s \in \operatorname{Bool},\; ((0 < \operatorname{det}\left(A\right)) \land B = \operatorname{act}\left(\operatorname{realCast}\left(A\right), \operatorname{sectorModel}\left(\mathrm{i}, t, s\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.lorentzian_model_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

The phase conditions require the mixed wedge Gram matrix to vanish, the cubic density to equal its entrywise conjugate, and the mean trace of the Gram matrix to be purely imaginary. The real symmetric cubic density has negative determinant. Its spectral factorization gives an oriented real coframe with the required Gram scalar and cubic density. These two quantities determine a common Hodge eigenspace and leave a complex orthogonal frame change of determinant one. A quaternion construction lifts that change to a real coframe action of determinant one. Conversely, the model and every positively oriented real coframe image satisfy the phase conditions.

**Theorem 1.14 (Hodge eigenvalues of the oriented sectors).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall z \in K,\; \forall A \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall t \in \operatorname{Bool},\; \forall s \in \operatorname{Bool},\; ((z^{4} = 1 \land \operatorname{det}\left(A\right) \ne 0) \implies \operatorname{hodge}\left(A \cdot \operatorname{modelMetric}\left(z\right) \cdot (A)^{T}, \operatorname{det}\left(A\right)\right) \cdot \operatorname{act}\left(A, \operatorname{sectorModel}\left(z, t, s\right)\right) = (z \cdot \operatorname{signValue}\left(s\right) \cdot \operatorname{act}\left(A, \operatorname{sectorModel}\left(z, t, s\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.oriented_sector_hodge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Use the coframe determinant as the volume coefficient. The overall sign affects the cubic density and cancels in the exterior square used by the Hodge operator. The second label gives the Hodge eigenvalue. It is plus or minus one for the Euclidean model and plus or minus the imaginary unit for the Lorentzian model, with true denoting self-duality in both cases.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.degenerate_simplicity_witnesses`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.euclidean_model_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.exists_graph_model`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.fixed_metric_sector_orbit_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.lorentzian_model_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.model_orbit_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.oriented_sector_hodge`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simple_iff_five_eq_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicityDeriv_surjective`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicity_expansion`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicity_jacobian_rank`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.simplicity_neg`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.urbantke_action`
- Truth anchor: `D5/S3/Geometry/Lorentz/PlebanskiSectors4D.wedgeGram_action`
- Dependency: [D5/S3/Geometry/Lorentz/Urbantke](Urbantke.md)
