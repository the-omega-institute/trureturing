# Kerr–Schild double copy in four dimensions

## Abstract

Exact curvature and projective double copies in four dimensions.

Use Cartesian coordinates with η = diag(−1, 1, 1, 1). Write p for the scalar φ, k for the lower covector, and n(k) for the contraction of k with its background-raised vector. The metric g is η + p k ⊗ k and ginv is η − p k♯ ⊗ k♯.

**Theorem 1.1 (Metric symmetry).**

$$\forall K \in \operatorname{Type},\; [\operatorname{CommRing}\left(K\right)] \forall p \in K,\; \forall k \in K^{4},\; (\operatorname{g}\left(p, k\right))^{T} = \operatorname{g}\left(p, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the background and the outer product are symmetric.

**Theorem 1.2 (Exact inverse).**

$$\forall K \in \operatorname{Type},\; [\operatorname{CommRing}\left(K\right)] \forall p \in K,\; \forall k \in K^{4},\; (\operatorname{n}\left(k\right) = 0 \implies (\operatorname{g}\left(p, k\right) \cdot \operatorname{ginv}\left(p, k\right) = 1 \land \operatorname{ginv}\left(p, k\right) \cdot \operatorname{g}\left(p, k\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_mul_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Monteiro, Donal O'Connell, Chris D. White (2014). *Black holes and the double copy*. DOI: [10.1007/JHEP12(2014)056](https://doi.org/10.1007/JHEP12(2014)056). URL: <https://arxiv.org/abs/1410.0239>.

*Commentary.*

The cross terms cancel, and nullity kills the product of the two rank-one terms.

**Theorem 1.3 (Rank-one determinant).**

$$\forall K \in \operatorname{Type},\; [\operatorname{CommRing}\left(K\right)] \forall p \in K,\; \forall k \in K^{4},\; \operatorname{det}\left(\operatorname{g}\left(p, k\right)\right) = - (1 + p \cdot \operatorname{n}\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_det_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor out η and apply the rank-one determinant identity.

**Theorem 1.4 (Determinant on the null cone).**

$$\forall K \in \operatorname{Type},\; [\operatorname{CommRing}\left(K\right)] \forall p \in K,\; \forall k \in K^{4},\; (\operatorname{n}\left(k\right) = 0 \implies \operatorname{det}\left(\operatorname{g}\left(p, k\right)\right) = - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant is constant along every null rank-one update.

For the unit lower time covector, n(k) = −1. The determinant is then −(1 − p), which differs from −1 whenever p is nonzero.

A jet j contains p, k and their first and symmetric second derivatives. N(j) imposes the nullity equation and its first two derivatives. G(j) imposes affine geodesicity and its first derivative. A first jet contains the values and first derivatives. Its conditions Nzero, Nfirst, and Gzero are nullity, differentiated nullity, and affine geodesicity, respectively. With h = p k ⊗ k, L is the Christoffel symbol of the first kind raised by η. Γ uses the same first-kind symbol raised by ginv. Its derivative applies the product rule to both factors. The mixed Ricci tensor R uses ginv to raise the first index after taking the full Ricci contraction. The linear expression Lin raises both contractions in the divergence of the first-kind symbol with η.

**Theorem 1.5 (Exact Christoffel decomposition).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall j \in \operatorname{FirstJet}\left(K\right),\; ((\operatorname{Nzero}\left(j\right) \land \operatorname{Nfirst}\left(j\right) \land \operatorname{Gzero}\left(j\right)) \implies \forall a \in \operatorname{Fin}\left(4\right),\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \Gamma\left(j, a, i, b\right) = \operatorname{L}\left(j, a, i, b\right) + \frac{\operatorname{phi}\left(j\right) \cdot \operatorname{along}\left(j\right) \cdot \operatorname{raised}\left(j, a\right) \cdot \operatorname{k}\left(j, i\right) \cdot \operatorname{k}\left(j, b\right)}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_christoffel_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative along k♯ is along(j) = k♯ · dp. The contraction of the first-kind symbol with k♯ yields the negative of this derivative times k ⊗ k divided by two.

**Theorem 1.6 (Vanishing connection trace).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall j \in \operatorname{FirstJet}\left(K\right),\; ((\operatorname{Nzero}\left(j\right) \land \operatorname{Nfirst}\left(j\right)) \implies \forall i \in \operatorname{Fin}\left(4\right),\; \sum_{a \in \operatorname{Fin}\left(4\right)} \Gamma\left(j, a, a, i\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_christoffel_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The flat trace vanishes by differentiated nullity. In the inverse correction, the two terms from differentiating along the traced indices cancel by exchanging those indices. The remaining term is proportional to the null contraction.

**Theorem 1.7 (Exact mixed Ricci linearity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall j \in \operatorname{Jet}\left(K\right),\; ((\operatorname{N}\left(j\right) \land \operatorname{G}\left(j\right)) \implies \forall i \in \operatorname{Fin}\left(4\right),\; \forall b \in \operatorname{Fin}\left(4\right),\; \operatorname{R}\left(j, i, b\right) = \operatorname{Lin}\left(j, i, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_mixed_ricci_linear_in_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Monteiro, Donal O'Connell, Chris D. White (2014). *Black holes and the double copy*. DOI: [10.1007/JHEP12(2014)056](https://doi.org/10.1007/JHEP12(2014)056). URL: <https://arxiv.org/abs/1410.0239>.

*Commentary.*

The divergence of the rank-one connection correction and the connection product leave a covariant term proportional to k ⊗ k. Contracting the flat divergence with k♯ identifies its coefficient and shows that raising with ginv cancels it. In indices Lin is half of ∂ⁱ∂ₐhᵃ_b + ∂_b∂ₐhⁱᵃ − ∂ᵃ∂ₐhⁱ_b.

**Theorem 1.8 (A null non-geodesic jet).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall p \in K,\; (p \ne 0 \implies (\operatorname{N}\left(\operatorname{Jbad}\left(p\right)\right) \land \neg \operatorname{G}\left(\operatorname{Jbad}\left(p\right)\right) \land \operatorname{R}\left(\operatorname{Jbad}\left(p\right), 0, 0\right) - \operatorname{Lin}\left(\operatorname{Jbad}\left(p\right), 0, 0\right) = 2 \cdot (p)^{2} \land \operatorname{R}\left(\operatorname{Jbad}\left(p\right), 0, 0\right) \ne \operatorname{Lin}\left(\operatorname{Jbad}\left(p\right), 0, 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_mixed_ricci_nongeodesic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the jet Jbad of (1, (1 − t²)/(1 + t²), 2t/(1 + t²), 0) at zero and hold p constant. The only nonzero derivatives are the time derivative of the second spatial component and the second time derivative of the first spatial component.

S(j) means time independence through order two and k₀ = 1 with its first and second derivatives zero. The potential is A = p k, its field strength is Fₐᵦ = ∂ₐAᵦ − ∂ᵦAₐ, and Max is ∂ₐFᵃⁱ. Lap denotes the sum of the three spatial diagonal second derivatives of p.

**Theorem 1.9 (Stationary Maxwell copy).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall j \in \operatorname{Jet}\left(K\right),\; ((\operatorname{N}\left(j\right) \land \operatorname{G}\left(j\right)) \implies (\operatorname{S}\left(j\right) \implies \forall i \in \operatorname{Fin}\left(4\right),\; (\operatorname{R}\left(j, i, 0\right) = \frac{- \operatorname{Max}\left(j, i\right)}{2} \land (\operatorname{R}\left(j, i, 0\right) = 0 \iff \operatorname{Max}\left(j, i\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.stationary_ks_ricci_maxwell_double_copy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Monteiro, Donal O'Connell, Chris D. White (2014). *Black holes and the double copy*. DOI: [10.1007/JHEP12(2014)056](https://doi.org/10.1007/JHEP12(2014)056). URL: <https://arxiv.org/abs/1410.0239>.

*Commentary.*

The mixed Ricci time column equals negative one half of the Maxwell divergence.

**Theorem 1.10 (Stationary scalar copy).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall j \in \operatorname{Jet}\left(K\right),\; ((\operatorname{N}\left(j\right) \land \operatorname{G}\left(j\right)) \implies (\operatorname{S}\left(j\right) \implies (\operatorname{R}\left(j, 0, 0\right) = \frac{\operatorname{Lap}\left(j\right)}{2} \land (\operatorname{R}\left(j, 0, 0\right) = 0 \iff \operatorname{Lap}\left(j\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.stationary_ks_ricci_poisson_zeroth_copy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ricardo Monteiro, Donal O'Connell, Chris D. White (2014). *Black holes and the double copy*. DOI: [10.1007/JHEP12(2014)056](https://doi.org/10.1007/JHEP12(2014)056). URL: <https://arxiv.org/abs/1410.0239>.

*Commentary.*

The lower time component of the potential is p, and raising its time index contributes a minus sign.

Ray denotes the complex projective line in the two stereographic charts. For a finite ray z use the affine factor X − z, and for infinity use the factor 1 of homogeneous degree one. The product f of the two factors has homogeneous degree two. The Maxwell quadratic q is a f, Q is its square, and C is the inverse Weyl quartic image of Q. W(D) denotes the Weyl quartic of D, m is projective multiplicity in degree four, and Tide is the complex screen tide. The symbol ev is projective quartic evaluation. At infinity the multiplicity is four minus the affine degree and evaluation uses the fourth coefficient.

**Theorem 1.11 (The type D quartic square).**

$$\forall a \in \mathbb{C},\; \forall r \in \operatorname{Ray},\; \forall s \in \operatorname{Ray},\; \forall t \in \operatorname{Ray},\; ((a \ne 0 \land r \ne s \land t \ne r \land t \ne s) \implies (\operatorname{Q}\left(a, r, s\right) = (\operatorname{q}\left(a, r, s\right))^{2} \land \operatorname{m}\left(r, \operatorname{Q}\left(a, r, s\right)\right) = 2 \land \operatorname{m}\left(s, \operatorname{Q}\left(a, r, s\right)\right) = 2 \land \operatorname{C}\left(a, r, s\right) \ne 0 \land \operatorname{Tide}\left(\operatorname{C}\left(a, r, s\right), t\right) = (a)^{2} \cdot \operatorname{ev}\left(t, (\operatorname{f}\left(r, s\right))^{2}\right) \land \forall D \in \operatorname{Weyl}_{4},\; ((D \ne 0 \land \operatorname{m}\left(r, \operatorname{W}\left(D\right)\right) = 2 \land \operatorname{m}\left(s, \operatorname{W}\left(D\right)\right) = 2 \land \operatorname{Tide}\left(D, t\right) = \operatorname{Tide}\left(\operatorname{C}\left(a, r, s\right), t\right)) \implies D = \operatorname{C}\left(a, r, s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.petrov_type_d_double_copy_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Luna, Ricardo Monteiro, Isobel Nicholson, Donal O'Connell (2019). *Type D Spacetimes and the Weyl Double Copy*. DOI: [10.1088/1361-6382/ab03e6](https://doi.org/10.1088/1361-6382/ab03e6). URL: <https://arxiv.org/abs/1810.08183>.

*Commentary.*

The two factors square, and evaluation at a third ray is nonzero for the unit amplitude. Every nonzero quartic with the two indicated double roots has the same two squared factors and a constant quotient. A tide at the third ray fixes that constant.

**Theorem 1.12 (Coulomb and Schwarzschild principal directions).**

$$\forall a \in \mathbb{C},\; (\operatorname{q}\left(a, 0, \infty\right) = a \cdot X \land \operatorname{Q}\left(a, 0, \infty\right) = (a)^{2} \cdot (X)^{2} \land \operatorname{Tide}\left(\operatorname{C}\left(a, 0, \infty\right), 1\right) = (a)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.coulomb_schwarzschild_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Luna, Ricardo Monteiro, Isobel Nicholson, Donal O'Connell (2019). *Type D Spacetimes and the Weyl Double Copy*. DOI: [10.1088/1361-6382/ab03e6](https://doi.org/10.1088/1361-6382/ab03e6). URL: <https://arxiv.org/abs/1810.08183>.

*Commentary.*

In the radial spin frame the two axial rays are zero and infinity. For nonzero amplitude the quartic gives the algebraic Schwarzschild type D pattern. The spacetime Weyl double copy also includes the scalar normalization relating the physical fields.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.coulomb_schwarzschild_quartic`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_christoffel_exact`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_christoffel_trace_zero`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_det`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_det_formula`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_mul_inv`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_metric_symm`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_mixed_ricci_linear_in_phi`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.ks_mixed_ricci_nongeodesic`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.petrov_type_d_double_copy_quartic`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.stationary_ks_ricci_maxwell_double_copy`
- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D.stationary_ks_ricci_poisson_zeroth_copy`
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
