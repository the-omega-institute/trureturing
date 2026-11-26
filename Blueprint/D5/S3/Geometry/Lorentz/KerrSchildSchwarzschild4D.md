# Schwarzschild and Coulomb Weyl double copy

## Abstract

The Schwarzschild and Coulomb fields in the radial screen frame.

At the unit-radius point on the positive third spatial axis, use the jet j of φ = p / |x| and k = (1, x / |x|). The frame T changes the Cartesian basis by the null rank-one term −p k♯ ⊗ k / 2. Write B for the pair matrix of the full Riemann curvature in T and C for the Ricci-free tensor with electric block diag(p/2, p/2, −p) and zero magnetic block. Max is the Cartesian divergence of the Coulomb field with both indices raised. The bivector order is 01, 02, 03, 23, 31, 12.

**Theorem 1.1 (The normalized Weyl square at unit radius).**

$$\forall p \in \mathbb{R},\; (p \ne 0 \implies ((\operatorname{T}\left(p\right))^{T} \cdot \operatorname{g}\left(p\right) \cdot \operatorname{T}\left(p\right) = \operatorname{eta} \land (\forall i \in \operatorname{PairIndex},\; \forall j \in \operatorname{PairIndex},\; \operatorname{C}\left(p, i, j\right) = \operatorname{B}\left(p, \operatorname{index}\left(i\right), \operatorname{index}\left(j\right)\right)) \land (\forall r \in \operatorname{Ray},\; \operatorname{CoulombScreen}\left(p, r\right) = \operatorname{ev}\left(2, r, \operatorname{q}\left(2 \cdot p, 0, \infty\right)\right)) \land (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{Max}\left(p, i\right) = 0) \land \operatorname{W}\left(\operatorname{C}\left(p\right)\right) = \frac{- 3}{p} \cdot \operatorname{Q}\left(2 \cdot p, 0, \infty\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/KerrSchildSchwarzschild4D.schwarzschild_coulomb_weyl_double_copy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Luna, Ricardo Monteiro, Isobel Nicholson, Donal O'Connell (2019). *Type D Spacetimes and the Weyl Double Copy*. DOI: [10.1088/1361-6382/ab03e6](https://doi.org/10.1088/1361-6382/ab03e6). URL: <https://arxiv.org/abs/1810.08183>.

*Commentary.*

The field strength of A = φ k has only F₀₃ = p and F₃₀ = −p. Its contraction with the screen vector and the null generator is the projective evaluation of the Maxwell quadratic 2pX in degree two. The orthonormal curvature has spatial pair block opposite to its electric block. The harmonic scalar gives the zero time component of the Maxwell divergence through the stationary Poisson identity. The spatial components vanish by the radial derivative equations. The Weyl contraction is −12pX², so the scalar multiplying the Maxwell square is −3/p in these conventions.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/KerrSchildSchwarzschild4D.schwarzschild_coulomb_weyl_double_copy`
- Dependency: [D5/S3/Geometry/Lorentz/KerrSchildDoubleCopy4D](KerrSchildDoubleCopy4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D](KerrSchildWeylDoubleCopy4D.md)
