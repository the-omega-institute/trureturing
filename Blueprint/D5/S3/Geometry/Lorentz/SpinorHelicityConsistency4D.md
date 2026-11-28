# Four-dimensional spinor helicity and four-point consistency

## Abstract

Spinor brackets and four-point consistency of polynomial channel restrictions.

Let K be a field. Spinors are two-component vectors. Both chiralities use the alternating bracket angle(u,v) = u(0)v(1) - u(1)v(0). The bispinor is the outer product l rᵀ. For four particles numbered 0 through 3, mandelstam(l,r,i,j) is the product of the two brackets of particles i and j. The prefactor H(l,r) is the square of angle(l(0),l(2)) times the square of angle(r(1),r(3)).

**Theorem 1.1 (Bracket antisymmetry).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall u v : (K)^{2}, (\operatorname{angle}\left(u, v\right) = (- \operatorname{angle}\left(v, u\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.angle_antisymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchange the two spinors in the alternating determinant.

**Theorem 1.2 (Vanishing on repeated spinors).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall u : (K)^{2}, (\operatorname{angle}\left(u, u\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.angle_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two products in the determinant cancel.

**Theorem 1.3 (Determinant covariance).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall A : \operatorname{Mat}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), K\right), (\forall u v : (K)^{2}, (\operatorname{angle}\left((A \cdot u), (A \cdot v)\right) = (\operatorname{det}\left(A\right) \cdot \operatorname{angle}\left(u, v\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.angle_det_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by a two-by-two matrix scales the bracket by its determinant. The bracket is invariant when this determinant is one.

**Theorem 1.4 (Schouten identity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall u v w z : (K)^{2}, (((\operatorname{angle}\left(u, v\right) \cdot \operatorname{angle}\left(w, z\right)) + (\operatorname{angle}\left(u, w\right) \cdot \operatorname{angle}\left(z, v\right)) + (\operatorname{angle}\left(u, z\right) \cdot \operatorname{angle}\left(v, w\right))) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.schouten_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expansion of the three products of alternating determinants cancels all monomials.

**Theorem 1.5 (Determinant-one frame transport).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall u v w x y z : (K)^{2}, (((\operatorname{angle}\left(u, v\right) \neq 0) \land (\operatorname{angle}\left(u, v\right) = \operatorname{angle}\left(x, y\right)) \land (\operatorname{angle}\left(u, w\right) = \operatorname{angle}\left(x, z\right)) \land (\operatorname{angle}\left(v, w\right) = \operatorname{angle}\left(y, z\right))) \implies (\exists A \in \operatorname{Mat}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), K\right),\; ((\operatorname{det}\left(A\right) = 1) \land ((A \cdot u) = x) \land ((A \cdot v) = y) \land ((A \cdot w) = z)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spinor_frame_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero bracket determines a basis. Schouten expresses the third spinor in that basis using its two brackets. Equality of the three brackets constructs a determinant-one matrix transporting the two frames and the third spinor.

**Theorem 1.6 (Null bispinor).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall l r : (K)^{2}, (\operatorname{det}\left(\operatorname{bispinor}\left(l, r\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.bispinor_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the outer product vanishes.

**Theorem 1.7 (Mandelstam determinant).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall l_{1} r_{1} l_{2} r_{2} : (K)^{2}, (\operatorname{det}\left((\operatorname{bispinor}\left(l_{1}, r_{1}\right) + \operatorname{bispinor}\left(l_{2}, r_{2}\right))\right) = (\operatorname{angle}\left(l_{1}, l_{2}\right) \cdot \operatorname{angle}\left(r_{1}, r_{2}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.mandelstam_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the determinant of a sum of two outer products only the mixed terms survive.

**Theorem 1.8 (Null bispinor factorization).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall A : \operatorname{Mat}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), K\right), ((\operatorname{det}\left(A\right) = 0) \iff (\exists l \in (K)^{2},\; (\exists r \in (K)^{2},\; (A = \operatorname{bispinor}\left(l, r\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.null_bispinor_factorization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A matrix with vanishing determinant and a nonzero entry has proportional rows and columns, giving an outer-product factorization by division at that entry. The zero matrix also factors.

**Theorem 1.9 (Three-point complex kinematics).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall l_{1} l_{2} l_{3} r_{1} r_{2} r_{3} : (K)^{2}, (((\operatorname{bispinor}\left(l_{1}, r_{1}\right) + \operatorname{bispinor}\left(l_{2}, r_{2}\right) + \operatorname{bispinor}\left(l_{3}, r_{3}\right)) = 0) \implies (((\operatorname{angle}\left(l_{1}, l_{2}\right) = 0) \land (\operatorname{angle}\left(l_{2}, l_{3}\right) = 0) \land (\operatorname{angle}\left(l_{3}, l_{1}\right) = 0)) \lor ((\operatorname{angle}\left(r_{1}, r_{2}\right) = 0) \land (\operatorname{angle}\left(r_{2}, r_{3}\right) = 0) \land (\operatorname{angle}\left(r_{3}, r_{1}\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_kinematics_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a left bracket is nonzero, its spinors are independent, and momentum conservation expresses their right spinors as multiples of the third. Hence all right brackets vanish. The complementary case has all left brackets zero.

**Theorem 1.10 (Conjugate spinors).**

$$(\forall l_{1} l_{2} l_{3} : (\mathbb{C})^{2}, (((\operatorname{bispinor}\left(l_{1}, \overline{l_{1}}\right) + \operatorname{bispinor}\left(l_{2}, \overline{l_{2}}\right) + \operatorname{bispinor}\left(l_{3}, \overline{l_{3}}\right)) = 0) \implies (((\operatorname{angle}\left(l_{1}, l_{2}\right) = 0) \land (\operatorname{angle}\left(l_{2}, l_{3}\right) = 0) \land (\operatorname{angle}\left(l_{3}, l_{1}\right) = 0)) \land ((\operatorname{angle}\left(\overline{l_{1}}, \overline{l_{2}}\right) = 0) \land (\operatorname{angle}\left(\overline{l_{2}}, \overline{l_{3}}\right) = 0) \land (\operatorname{angle}\left(\overline{l_{3}}, \overline{l_{1}}\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_real_brackets_vanish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For right spinors equal to the conjugates of the left spinors, the right brackets are conjugates of the left brackets. Consequently both sets vanish.

**Theorem 1.11 (Scaled conjugate spinors).**

$$(\forall l_{1} l_{2} l_{3} : (\mathbb{C})^{2}, (\forall a b c : \mathbb{C}, (((a \neq 0) \land (b \neq 0) \land (c \neq 0) \land ((\operatorname{bispinor}\left(l_{1}, (a \cdot \overline{l_{1}})\right) + \operatorname{bispinor}\left(l_{2}, (b \cdot \overline{l_{2}})\right) + \operatorname{bispinor}\left(l_{3}, (c \cdot \overline{l_{3}})\right)) = 0)) \implies (((\operatorname{angle}\left(l_{1}, l_{2}\right) = 0) \land (\operatorname{angle}\left(l_{2}, l_{3}\right) = 0) \land (\operatorname{angle}\left(l_{3}, l_{1}\right) = 0)) \land ((\operatorname{angle}\left((a \cdot \overline{l_{1}}), (b \cdot \overline{l_{2}})\right) = 0) \land (\operatorname{angle}\left((b \cdot \overline{l_{2}}), (c \cdot \overline{l_{3}})\right) = 0) \land (\operatorname{angle}\left((c \cdot \overline{l_{3}}), (a \cdot \overline{l_{1}})\right) = 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_scaled_conjugate_brackets_vanish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonzero scalar multiples of the conjugate spinors multiply each conjugate bracket by a nonzero factor. Both bracket families vanish under momentum conservation. Real signs allow both time orientations.

**Theorem 1.12 (Unique three-point exponents).**

$$(\forall h_{1} h_{2} h_{3} d_{1} d_{2} d_{3} : \mathbb{Z}, ((((d_{2} + d_{3}) = ((- 2) \cdot h_{1})) \land ((d_{3} + d_{1}) = ((- 2) \cdot h_{2})) \land ((d_{1} + d_{2}) = ((- 2) \cdot h_{3}))) \iff ((d_{1} = ((h_{1} - h_{2}) - h_{3})) \land (d_{2} = ((h_{2} - h_{3}) - h_{1})) \land (d_{3} = ((h_{3} - h_{1}) - h_{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_little_group_exponents_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding two scaling equations and subtracting the third isolates twice one exponent. This determines each integer exponent uniquely.

**Theorem 1.13 (Parke–Taylor polynomial identity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall l r : (\operatorname{Fin}\left(4\right) \to (K)^{2}), ((\sum_{i:\operatorname{Fin}\left(4\right)} (\operatorname{bispinor}\left(l\left(i\right), r\left(i\right)\right)) = 0) \implies ((\operatorname{H}\left(l, r\right) \cdot (\operatorname{angle}\left(l\left(0\right), l\left(1\right)\right) \cdot \operatorname{angle}\left(l\left(1\right), l\left(2\right)\right) \cdot \operatorname{angle}\left(l\left(2\right), l\left(3\right)\right) \cdot \operatorname{angle}\left(l\left(3\right), l\left(0\right)\right))) = (- ((\operatorname{angle}\left(l\left(0\right), l\left(2\right)\right))^{4} \cdot \operatorname{mandelstam}\left(l, r, 0, 1\right) \cdot \operatorname{mandelstam}\left(l, r, 0, 3\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_parke_taylor_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Contract momentum conservation on the left with spinor 2 and on the right with spinors 1 and 3. Multiplying the resulting two identities and using antisymmetry gives the signed, denominator-cleared relation even at zero brackets.

**Theorem 1.14 (Parke–Taylor ratio).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall l r : (\operatorname{Fin}\left(4\right) \to (K)^{2}), (((\sum_{i:\operatorname{Fin}\left(4\right)} (\operatorname{bispinor}\left(l\left(i\right), r\left(i\right)\right)) = 0) \land ((\operatorname{mandelstam}\left(l, r, 0, 1\right) \cdot \operatorname{mandelstam}\left(l, r, 0, 3\right)) \neq 0) \land ((\operatorname{angle}\left(l\left(0\right), l\left(1\right)\right) \cdot \operatorname{angle}\left(l\left(1\right), l\left(2\right)\right) \cdot \operatorname{angle}\left(l\left(2\right), l\left(3\right)\right) \cdot \operatorname{angle}\left(l\left(3\right), l\left(0\right)\right)) \neq 0)) \implies (\frac{\operatorname{H}\left(l, r\right)}{(\operatorname{mandelstam}\left(l, r, 0, 1\right) \cdot \operatorname{mandelstam}\left(l, r, 0, 3\right))} = (- \frac{(\operatorname{angle}\left(l\left(0\right), l\left(2\right)\right))^{4}}{(\operatorname{angle}\left(l\left(0\right), l\left(1\right)\right) \cdot \operatorname{angle}\left(l\left(1\right), l\left(2\right)\right) \cdot \operatorname{angle}\left(l\left(2\right), l\left(3\right)\right) \cdot \operatorname{angle}\left(l\left(3\right), l\left(0\right)\right))}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_parke_taylor_mandelstam_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Where the two denominators are nonzero, division of the polynomial identity gives the ratio. The minus sign follows from the oriented last bracket and the determinant convention.

**Theorem 1.15 (Four-point KLT product).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall k s t u : K, (((- s) \cdot \frac{k}{(s \cdot t)} \cdot \frac{k}{(s \cdot u)}) = \frac{(- (k)^{2})}{(s \cdot t \cdot u)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_klt_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational product has the KLT channel denominators and a squared prefactor. The identity also holds with total field division at zero denominators.

**Theorem 1.16 (KLT product of ordered Parke–Taylor ratios).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall l r : (\operatorname{Fin}\left(4\right) \to (K)^{2}), (((\sum_{i:\operatorname{Fin}\left(4\right)} (\operatorname{bispinor}\left(l\left(i\right), r\left(i\right)\right)) = 0) \land ((\operatorname{mandelstam}\left(l, r, 0, 1\right) \cdot \operatorname{mandelstam}\left(l, r, 0, 3\right)) \neq 0) \land ((\operatorname{mandelstam}\left(l, r, 0, 1\right) \cdot \operatorname{mandelstam}\left(l, r, 0, 2\right)) \neq 0) \land ((\operatorname{angle}\left(l\left(0\right), l\left(1\right)\right) \cdot \operatorname{angle}\left(l\left(1\right), l\left(2\right)\right) \cdot \operatorname{angle}\left(l\left(2\right), l\left(3\right)\right) \cdot \operatorname{angle}\left(l\left(3\right), l\left(0\right)\right)) \neq 0) \land ((\operatorname{angle}\left(l\left(0\right), l\left(1\right)\right) \cdot \operatorname{angle}\left(l\left(1\right), l\left(3\right)\right) \cdot \operatorname{angle}\left(l\left(3\right), l\left(2\right)\right) \cdot \operatorname{angle}\left(l\left(2\right), l\left(0\right)\right)) \neq 0)) \implies (((- \operatorname{mandelstam}\left(l, r, 0, 1\right)) \cdot \frac{(\operatorname{angle}\left(l\left(0\right), l\left(2\right)\right))^{4}}{(\operatorname{angle}\left(l\left(0\right), l\left(1\right)\right) \cdot \operatorname{angle}\left(l\left(1\right), l\left(2\right)\right) \cdot \operatorname{angle}\left(l\left(2\right), l\left(3\right)\right) \cdot \operatorname{angle}\left(l\left(3\right), l\left(0\right)\right))} \cdot \frac{(\operatorname{angle}\left(l\left(0\right), l\left(2\right)\right))^{4}}{(\operatorname{angle}\left(l\left(0\right), l\left(1\right)\right) \cdot \operatorname{angle}\left(l\left(1\right), l\left(3\right)\right) \cdot \operatorname{angle}\left(l\left(3\right), l\left(2\right)\right) \cdot \operatorname{angle}\left(l\left(2\right), l\left(0\right)\right))}) = \frac{(- (\operatorname{H}\left(l, r\right))^{2})}{(\operatorname{mandelstam}\left(l, r, 0, 1\right) \cdot \operatorname{mandelstam}\left(l, r, 0, 3\right) \cdot \operatorname{mandelstam}\left(l, r, 0, 2\right))})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_klt_parke_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair momentum conservation equates the complementary Mandelstam determinants. The second ordering has the signed ratio with denominator s12 s13. The two minus signs cancel in the KLT product.

For a polynomial P in K[s,t], write evalS(P) = P(0,X), evalT(P) = P(X,0), and evalU(P) = P(X,-X), each in K[X]. The map C embeds a scalar as a constant polynomial. The constant terms of the three restrictions agree. The linear coefficient on the third line equals the linear coefficient on the second minus that on the first. These relations hold for arbitrary polynomial degree. The following compatibility conditions concern tree numerator polynomials with the stated channel restrictions for their factorization residues.

**Theorem 1.17 (Spin-one channel consistency).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall c_{s} c_{t} c_{u} : K, ((\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), K\right),\; ((\operatorname{evalS}\left(P\right) = (\operatorname{C}\left(c_{s}\right) \cdot X)) \land (\operatorname{evalT}\left(P\right) = (\operatorname{C}\left((- c_{t})\right) \cdot X)) \land (\operatorname{evalU}\left(P\right) = (\operatorname{C}\left(c_{u}\right) \cdot X)))) \iff ((c_{s} + c_{t} + c_{u}) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spin_one_four_point_consistency_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Necessity follows by comparing the linear coefficients. Sufficiency is realized by the polynomial -c_t s + c_s t.

**Theorem 1.18 (Spin-two channel consistency).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall c_{s} c_{t} c_{u} : K, ((\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), K\right),\; ((\operatorname{evalS}\left(P\right) = \operatorname{C}\left(c_{s}\right)) \land (\operatorname{evalT}\left(P\right) = \operatorname{C}\left(c_{t}\right)) \land (\operatorname{evalU}\left(P\right) = \operatorname{C}\left(c_{u}\right)))) \iff ((c_{s} = c_{t}) \land (c_{t} = c_{u}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spin_two_four_point_consistency_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of constant terms forces all three residues to agree. A constant polynomial realizes every such triple.

**Theorem 1.19 (Universal nonzero coupling).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall k_{g} k_{a} : K, ((\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), K\right),\; ((\operatorname{evalS}\left(P\right) = \operatorname{C}\left((k_{g} \cdot k_{a})\right)) \land (\operatorname{evalT}\left(P\right) = \operatorname{C}\left((k_{a})^{2}\right)) \land (\operatorname{evalU}\left(P\right) = \operatorname{C}\left((k_{a})^{2}\right)))) \iff ((k_{a} = 0) \lor (k_{a} = k_{g}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.equivalence_principle_from_consistency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spin-two condition on the single-graviton and species couplings is k_g k_a = k_a². A field has no zero divisors, so each coupled species has the graviton self-coupling.

**Theorem 1.20 (Higher-spin channel exclusion).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] (\forall s : \mathbb{N}, (\forall c_{s} c_{t} c_{u} : K, ((3 \leq s) \implies ((\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), K\right),\; ((((X)^{(s - 2)} \cdot \operatorname{evalS}\left(P\right)) = \operatorname{C}\left(c_{s}\right)) \land (((X)^{(s - 2)} \cdot \operatorname{evalT}\left(P\right)) = \operatorname{C}\left((((- 1))^{s} \cdot c_{t})\right)) \land (((X)^{(s - 2)} \cdot \operatorname{evalU}\left(P\right)) = \operatorname{C}\left(c_{u}\right)))) \iff ((c_{s} = 0) \land (c_{t} = 0) \land (c_{u} = 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.higher_spin_four_point_exclusion_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For spin at least three, the positive power of X annihilates the constant coefficient on each line. All three prescribed constants must therefore vanish. The zero polynomial suffices when they vanish.

Let I be a finite type of species. The coupling f is totally antisymmetric under adjacent exchanges for spin one. For spin two, a totally symmetric cubic coupling g determines the matrix M(g,a) with entry (b,c) equal to g(a,b,c). Its species product Q(g,x,y) is the sum of x(a) M(g,a)y over a.

**Theorem 1.21 (Jacobi identity from color residues).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] (\forall f : (I \to (I \to (I \to K))), ((\forall a b c : I, ((f\left(a, b, c\right) = (- f\left(b, a, c\right))) \land (f\left(a, b, c\right) = (- f\left(a, c, b\right))))) \implies (\forall a b c d : I, ((\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), K\right),\; ((\operatorname{evalS}\left(P\right) = (\operatorname{C}\left(\sum_{e:I} ((f\left(a, b, e\right) \cdot f\left(c, d, e\right)))\right) \cdot X)) \land (\operatorname{evalT}\left(P\right) = (\operatorname{C}\left((- \sum_{e:I} ((f\left(a, d, e\right) \cdot f\left(b, c, e\right))))\right) \cdot X)) \land (\operatorname{evalU}\left(P\right) = (\operatorname{C}\left(\sum_{e:I} ((f\left(a, c, e\right) \cdot f\left(d, b, e\right)))\right) \cdot X)))) \implies (\sum_{e:I} (((f\left(a, b, e\right) \cdot f\left(e, c, d\right)) + (f\left(b, c, e\right) \cdot f\left(e, a, d\right)) + (f\left(c, a, e\right) \cdot f\left(e, b, d\right)))) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spin_one_jacobi_from_consistency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spin-one compatibility condition forces the sum of the three contracted color factors to vanish. Total antisymmetry converts them to the ordinary Jacobi contraction.

**Theorem 1.22 (Commutativity and associativity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] (\forall g : (I \to (I \to (I \to K))), ((\forall a b c : I, ((g\left(a, b, c\right) = g\left(b, a, c\right)) \land (g\left(a, b, c\right) = g\left(a, c, b\right)))) \implies ((\forall a b c d : I, ((\sum_{e:I} ((g\left(a, b, e\right) \cdot g\left(c, d, e\right))) = \sum_{e:I} ((g\left(a, d, e\right) \cdot g\left(b, c, e\right)))) \land (\sum_{e:I} ((g\left(a, d, e\right) \cdot g\left(b, c, e\right))) = \sum_{e:I} ((g\left(a, c, e\right) \cdot g\left(d, b, e\right)))))) \iff (\forall a b : I, (((\operatorname{M}\left(g, a\right) \cdot \operatorname{M}\left(g, b\right)) = (\operatorname{M}\left(g, b\right) \cdot \operatorname{M}\left(g, a\right))) \land ((\operatorname{M}\left(g, a\right) \cdot \operatorname{M}\left(g, b\right)) = \sum_{e:I} ((g\left(a, b, e\right) \cdot \operatorname{M}\left(g, e\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.multi_graviton_commutativity_and_decoupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each matrix product entry is one of the three residue contractions. Total symmetry identifies the reversed product with the second contraction and the weighted sum of matrices with the first.

**Theorem 1.23 (Independent joint eigenvectors decouple).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] (\forall g : (I \to (I \to (I \to K))), ((\forall a b c : I, ((g\left(a, b, c\right) = g\left(b, a, c\right)) \land (g\left(a, b, c\right) = g\left(a, c, b\right)))) \implies (\forall x y chi psi : (I \to K), (((\forall a : I, (((\operatorname{M}\left(g, a\right) \cdot x) = (chi\left(a\right) \cdot x)) \land ((\operatorname{M}\left(g, a\right) \cdot y) = (psi\left(a\right) \cdot y)))) \land \operatorname{LinearIndependent}\left(K, [x,y]\right)) \implies (\operatorname{Q}\left(g, x, y\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.graviton_cross_product_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetry makes the species product commutative. For two common eigenvectors it is simultaneously a scalar multiple of each. Linear independence makes both scalars vanish.

**Theorem 1.24 (Joint eigenspaces span the real species space).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] (\forall g : (I \to (I \to (I \to \mathbb{R}))), (((\forall a b c : I, ((g\left(a, b, c\right) = g\left(b, a, c\right)) \land (g\left(a, b, c\right) = g\left(a, c, b\right)))) \land (\forall a b c d : I, ((\sum_{e:I} ((g\left(a, b, e\right) \cdot g\left(c, d, e\right))) = \sum_{e:I} ((g\left(a, d, e\right) \cdot g\left(b, c, e\right)))) \land (\sum_{e:I} ((g\left(a, d, e\right) \cdot g\left(b, c, e\right))) = \sum_{e:I} ((g\left(a, c, e\right) \cdot g\left(d, b, e\right))))))) \implies (\operatorname{sup}_{chi:(I \to \mathbb{R})} \operatorname{inf}_{a:I} \operatorname{eigenspace}\left(\operatorname{toEuclideanLin}\left(\operatorname{M}\left(g, a\right)\right), chi\left(a\right)\right) = \operatorname{top})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.multi_graviton_joint_eigenspaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residue equations make the real symmetric coupling matrices commute. The joint eigenspaces of the corresponding Euclidean linear operators exhaust the species space. Common eigenvectors can be chosen as a basis, and the preceding vanishing identity eliminates mixed products of distinct basis vectors.

**Theorem 1.25 (A decoupled basis of species).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] (\forall g : (I \to (I \to (I \to \mathbb{R}))), (((\forall a b c : I, ((g\left(a, b, c\right) = g\left(b, a, c\right)) \land (g\left(a, b, c\right) = g\left(a, c, b\right)))) \land (\forall a b c d : I, ((\sum_{e:I} ((g\left(a, b, e\right) \cdot g\left(c, d, e\right))) = \sum_{e:I} ((g\left(a, d, e\right) \cdot g\left(b, c, e\right)))) \land (\sum_{e:I} ((g\left(a, d, e\right) \cdot g\left(b, c, e\right))) = \sum_{e:I} ((g\left(a, c, e\right) \cdot g\left(d, b, e\right))))))) \implies (\exists B \in \operatorname{Basis}\left(I, \mathbb{R}, (I \to \mathbb{R})\right),\; ((\forall i : I, (\exists chi \in (I \to \mathbb{R}),\; (\forall a : I, ((\operatorname{M}\left(g, a\right) \cdot B\left(i\right)) = (chi\left(a\right) \cdot B\left(i\right)))))) \land (\forall i j : I, ((i \neq j) \implies (\operatorname{Q}\left(g, B\left(i\right), B\left(j\right)\right) = 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.multi_graviton_decoupled_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of joint eigenvectors spans the Euclidean species space. A basis extracted from this spanning set transports to species coordinate space. Products between distinct basis vectors vanish by their linear independence.

**Theorem 1.26 (A noncommuting symmetric two-species coupling).**

$$(\exists g \in (\operatorname{Fin}\left(2\right) \to (\operatorname{Fin}\left(2\right) \to (\operatorname{Fin}\left(2\right) \to \mathbb{R}))),\; ((\forall a b c : \operatorname{Fin}\left(2\right), ((g\left(a, b, c\right) = g\left(b, a, c\right)) \land (g\left(a, b, c\right) = g\left(a, c, b\right)))) \land ((\operatorname{M}\left(g, 0\right) \cdot \operatorname{M}\left(g, 1\right)) \neq (\operatorname{M}\left(g, 1\right) \cdot \operatorname{M}\left(g, 0\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.two_graviton_noncommuting_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take g(a,b,c) equal to one when exactly one of the three indices is 1, and zero otherwise. The (0,1) entries of the two ordered matrix products differ.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.angle_antisymm`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.angle_det_covariance`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.angle_self`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.bispinor_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.equivalence_principle_from_consistency`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_klt_identity`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_klt_parke_taylor`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_parke_taylor_mandelstam_identity`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.four_point_parke_taylor_polynomial`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.graviton_cross_product_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.higher_spin_four_point_exclusion_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.mandelstam_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.multi_graviton_commutativity_and_decoupling`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.multi_graviton_decoupled_basis`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.multi_graviton_joint_eigenspaces`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.null_bispinor_factorization_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.schouten_identity`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spin_one_four_point_consistency_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spin_one_jacobi_from_consistency`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spin_two_four_point_consistency_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.spinor_frame_transport`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_kinematics_dichotomy`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_little_group_exponents_unique`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_real_brackets_vanish`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.three_point_scaled_conjugate_brackets_vanish`
- Truth anchor: `D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D.two_graviton_noncommuting_example`
