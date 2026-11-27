# The Urbantke conformal metric from three two-forms

## Abstract

Universal Urbantke metric identities, chiral reconstruction and Lorentzian conformal reality.

A triple of two-forms in dimension four determines a cubic metric density U. The density is invertible exactly when the wedge Gram matrix Q is invertible. In that case the triple spans a chiral plane and determines one conformal class.

**Theorem 1.1 (Universal polynomial identities).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; ((\operatorname{U}\left(B\right))^{T} = \operatorname{U}\left(B\right) \land \operatorname{det}\left(\operatorname{U}\left(B\right)\right) = \frac{(\operatorname{det}\left(\operatorname{Q}\left(B\right)\right))^{2}}{64} \land \Lambda^{2}\left(\operatorname{U}\left(B\right)\right) \cdot \operatorname{W}\left(K\right) \cdot B = (\frac{\operatorname{det}\left(\operatorname{Q}\left(B\right)\right)}{8} \cdot B))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.urbantke_polynomial_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Order the bivectors as (01, 02, 03, 23, 31, 12), so W exchanges the first and last blocks of three coordinates. Write Q(B) = BᵀWB and D(B) = det Q(B)/8. The symbols ε(i,j,k) and ε(c,d,e,f) equal 1 on the increasing tuples. The entry U(a,b) contracts their product against B(a,c,i)B(b,d,j)B(e,f,k) with coefficient 1/12. The internal contraction is a determinant of three rows. In the alternating spacetime contraction, interchanging the last two indices contributes a second equal term. This gives the coefficient 1/6 in the oriented-pair sum from the coefficient 1/12 in the full contraction. When the electric block E is invertible, changing the internal basis by its inverse puts the triple on the graph [I; H]. The determinant of the basis change scales U once and D twice. The symmetric part S of H gives Q = 2S. The skew part gives a determinant-one coframe shear L, and the cubic is Lᵀ diag(1, adj S) L. The determinant of adj S is (det S)², and the spatial second exterior block of adj S is (det S)S. Together with adj S · S = (det S)I these prove the identities in the symmetric chart, including singular S. Exterior wedge covariance transports the minor identity through L. After undoing the internal basis change, replace E by E + tI. Its determinant is a monic cubic in t. Each claimed entry identity holds at infinitely many t, so its polynomial difference vanishes at t = 0.

**Theorem 1.2 (Nondegeneracy and the chiral plane).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; ((\operatorname{det}\left(\operatorname{U}\left(B\right)\right) \ne 0 \iff \operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0) \land (\operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0 \implies (\operatorname{LinearIndependent}\left(K, \operatorname{columns}\left(B\right)\right) \land \operatorname{dim}\left(\operatorname{Col}\left(B\right)\right) = 3 \land (\operatorname{H}\left(\operatorname{U}\left(B\right), \operatorname{D}\left(B\right)\right))^{2} = I_{6} \land \operatorname{H}\left(\operatorname{U}\left(B\right), \operatorname{D}\left(B\right)\right) \cdot B = B \land (\forall x \in K^{6},\; (\operatorname{H}\left(\operatorname{U}\left(B\right), \operatorname{D}\left(B\right)\right) \cdot x = x \iff \exists y \in K^{3},\; B \cdot y = x)) \land (\forall x \in K^{6},\; (\operatorname{H}\left(\operatorname{U}\left(B\right), \operatorname{D}\left(B\right)\right) \cdot x = - x \iff (B)^{T} \cdot \operatorname{W}\left(K\right) \cdot x = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.urbantke_nondegenerate_iff_and_chiral_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant identity gives the nondegeneracy equivalence. Invertibility of Q makes multiplication by B injective, so the columns span a three-dimensional subspace. The two-form Hodge operator is H = DW(Λ²U)⁻¹. The wedge determinant identity gives H² = I, and the minor identity says H fixes B. Complementary oriented minors give trace H = 0. The projector (I + H)/2 has trace and rank three, so its range is the column span. The opposite eigenspace is its W-orthogonal complement by W-self-adjointness and the invertibility of Q.

**Theorem 1.3 (Scalar rigidity of the second exterior power).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall A \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall c \in K,\; ((c \ne 0 \land \Lambda^{2}\left(A\right) = (c \cdot I_{6})) \implies \exists r \in K,\; (r \ne 0 \land A = (r \cdot I_{4})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.exteriorSquare_eq_smul_id_imp_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proportionality of the oriented minors gives proportionality in either orientation of a pair. For distinct row indices k and i, choose j distinct from both. The principal minor in i,j is nonzero, and the two minors with rows k,j and k,i and columns i,j vanish. Eliminating the off-diagonal entries gives Aₖᵢ = 0. Each product of two distinct diagonal entries then equals c, so every diagonal entry is nonzero and the diagonal entries agree.

**Theorem 1.4 (Conformal uniqueness from exterior squares).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall g \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall h \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall c \in K,\; ((\operatorname{det}\left(g\right) \ne 0 \land c \ne 0 \land \Lambda^{2}\left(h\right) = (c \cdot \Lambda^{2}\left(g\right))) \implies \exists a \in K,\; (a \ne 0 \land h = (a \cdot g)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.urbantke_conformal_uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplicativity of exterior squares reduces the proportionality to a scalar exterior square for g₂g₁⁻¹. Scalar rigidity gives a nonzero factor relating the metrics.

**Theorem 1.5 (Conformal uniqueness from a chiral plane).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall g \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall h \in \operatorname{Mat}_{4 \times 4}\left(K\right),\; \forall v \in K,\; \forall w \in K,\; \forall B \in \operatorname{Mat}_{6 \times 3}\left(K\right),\; (((g)^{T} = g \land (h)^{T} = h \land \operatorname{det}\left(g\right) \ne 0 \land \operatorname{det}\left(h\right) \ne 0 \land (v)^{2} = \operatorname{det}\left(g\right) \land (w)^{2} = \operatorname{det}\left(h\right) \land \operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0 \land \operatorname{H}\left(g, v\right) \cdot B = B \land \operatorname{H}\left(h, w\right) \cdot B = B) \implies \exists a \in K,\; (a \ne 0 \land h = (a \cdot g)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.urbantke_conformal_uniqueness_of_chiral_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For volumes whose squares are the metric determinants, the stars square to the identity. Assigning the same wedge-nondegenerate plane eigenvalue +1 forces eigenvalue −1 on its W-orthogonal complement. These two subspaces span the bivector space, so the two stars agree. The exterior squares then differ by the ratio of volume coefficients.

**Theorem 1.6 (Lorentzian conformal reality).**

$$\forall B \in \operatorname{Mat}_{6 \times 3}\left(\mathbb{C}\right),\; ((\operatorname{det}\left(\operatorname{Q}\left(B\right)\right) \ne 0 \land (B)^{T} \cdot \operatorname{W}\left(\mathbb{C}\right) \cdot \overline{B} = 0) \implies \exists g \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \exists a \in \mathbb{C},\; (a \ne 0 \land (g)^{T} = g \land (\operatorname{det}\left(g\right) < 0) \land \operatorname{U}\left(B\right) = (a \cdot \operatorname{complexify}\left(g\right)) \land (\operatorname{H}\left(g, \sqrt{\lvert \operatorname{det}\left(g\right) \rvert}\right))^{2} = - I_{6}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.urbantke_lorentz_reality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reality equation places the conjugate plane in the opposite chiral eigenspace. Nondegeneracy gives the complementary decomposition, and conjugation reverses the sign of the normalized star. Conformal uniqueness makes the conjugate metric proportional to the original density. Dividing by a nonzero entry gives a real symmetric representative. In this real scale the complex volume is nonzero and purely imaginary, so the real determinant is negative. The positive real volume coefficient is the square root of the determinant's absolute value, and its Hodge operator squares to −I. A real nondegenerate symmetric form in four dimensions with negative determinant has one or three negative directions.

**Theorem 1.7 (The Lorentzian scalar graph).**

$$(\operatorname{Q}\left(\operatorname{graph}\left(\operatorname{i}\right)\right) = (2 \cdot \operatorname{i} \cdot I_{3}) \land \operatorname{U}\left(\operatorname{graph}\left(\operatorname{i}\right)\right) = \operatorname{diag}\left(1, - 1, - 1, - 1\right) \land (\operatorname{graph}\left(\operatorname{i}\right))^{T} \cdot \operatorname{W}\left(\mathbb{C}\right) \cdot \overline{\operatorname{graph}\left(\operatorname{i}\right)} = 0 \land \operatorname{D}\left(\operatorname{graph}\left(\operatorname{i}\right)\right) = - \operatorname{i})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.urbantke_lorentz_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the graph with lower block iI, the symmetric spatial block has adjugate −I and the coframe shear is the identity. The electric and magnetic blocks give the wedge Gram matrix 2iI, and replacing i by its conjugate in the second factor makes the mixed wedge Gram matrix zero.

**Theorem 1.8 (A simple complex triple without a real conformal metric).**

$$(\operatorname{Q}\left(\operatorname{graph}\left(1 + \operatorname{i}\right)\right) = (2 \cdot \left(1 + \operatorname{i}\right) \cdot I_{3}) \land \operatorname{det}\left(\operatorname{Q}\left(\operatorname{graph}\left(1 + \operatorname{i}\right)\right)\right) \ne 0 \land \operatorname{U}\left(\operatorname{graph}\left(1 + \operatorname{i}\right)\right) = \operatorname{diag}\left(1, 2 \cdot \operatorname{i}, 2 \cdot \operatorname{i}, 2 \cdot \operatorname{i}\right) \land \neg \exists g \in \operatorname{Mat}_{4 \times 4}\left(\mathbb{R}\right),\; \exists a \in \mathbb{C},\; \operatorname{U}\left(\operatorname{graph}\left(1 + \operatorname{i}\right)\right) = (a \cdot \operatorname{complexify}\left(g\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/Urbantke.simplicity_not_sufficient_for_real_lorentz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

For the graph with lower block (1+i)I, the wedge Gram matrix is a nonzero scalar multiple of I. Its Urbantke density has time entry 1 and spatial diagonal entries 2i. A complex scale making the time entry real must itself be real and nonzero. It then leaves the nonzero imaginary spatial entries nonreal.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.exteriorSquare_eq_smul_id_imp_scalar`
- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.simplicity_not_sufficient_for_real_lorentz`
- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.urbantke_conformal_uniqueness`
- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.urbantke_conformal_uniqueness_of_chiral_plane`
- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.urbantke_lorentz_reality`
- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.urbantke_lorentz_witness`
- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.urbantke_nondegenerate_iff_and_chiral_star`
- Truth anchor: `D5/S3/Geometry/Lorentz/Urbantke.urbantke_polynomial_identities`
