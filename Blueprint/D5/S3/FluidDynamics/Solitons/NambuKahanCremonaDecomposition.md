# A Cremona decomposition for quadratic Nambu systems

## Abstract

The homogeneous KHK map of a positive definite quadratic Nambu pair with a simple pencil factors through the cubic Cremona map.

**Definition 1.1 (The polarised Nambu matrix).**

$$\forall \left(A: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(B: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(x: \operatorname{Fin}\left(3\right) \to \mathbb{C}\right), \left(\operatorname{nambuLinearPart}\left(A, B, x\right) = \left(\left(i: \operatorname{Fin}\left(3\right)\right) \mapsto \left(\left(\left(j: \operatorname{Fin}\left(3\right)\right) \mapsto \left(\operatorname{crossProduct}\left(\operatorname{Matrix.mulVec}\left(\operatorname{Matrix.map}\left(A, \operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right), x\right), \operatorname{Matrix.mulVec}\left(\operatorname{Matrix.map}\left(B, \operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right), \operatorname{Pi.single}\left(j, \left(1: \mathbb{C}\right)\right)\right)\right)\left(i\right) + \operatorname{crossProduct}\left(\operatorname{Matrix.mulVec}\left(\operatorname{Matrix.map}\left(A, \operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right), \operatorname{Pi.single}\left(j, \left(1: \mathbb{C}\right)\right)\right), \operatorname{Matrix.mulVec}\left(\operatorname{Matrix.map}\left(B, \operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right), x\right)\right)\left(i\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.nambuLinearPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michele Graffeo, Giorgio Gubbiotti (2024). *Growth and Integrability of Some Birational Maps in Dimension Three*. DOI: [10.1007/s00023-023-01339-5](https://doi.org/10.1007/s00023-023-01339-5). URL: <https://arxiv.org/abs/2301.09129v2>.

*Commentary.*

For real matrices A and B and a complex vector x, the jth column is the sum of the cross products of Ax with the jth column of B and of the jth column of A with Bx. The real entries are included in the complex numbers by algebraMap. Pi.single j 1 is the jth coordinate vector. Thus multiplication by a vector v gives Ax × Bv + Av × Bx. For symmetric A and B twice this expression is the symmetric polarisation of the Nambu vector field with Hamiltonians xᵀAx and xᵀBx. The Nambu system appears in Remark 7.7, TeX lines 3180–3195; the displayed matrix is its complex coordinate encoding.

**Definition 1.2 (The homogeneous KHK matrix).**

$$\forall \left(A: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(B: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(h: \mathbb{R}\right), \left(\forall \left(X: \operatorname{Fin}\left(4\right) \to \mathbb{C}\right), \left(\operatorname{kahanMatrix}\left(A, B, h, X\right) = \operatorname{HSMul.hSMul}\left(X\left(\left(3: \operatorname{Fin}\left(4\right)\right)\right), \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)\right) - \operatorname{HSMul.hSMul}\left(\left(\left(2: \mathbb{C}\right)\right) \cdot \left(\left(h: \mathbb{C}\right)\right), \operatorname{nambuLinearPart}\left(A, B, \left(\left(i: \operatorname{Fin}\left(3\right)\right) \mapsto \left(X\left(\operatorname{Fin.castSucc}\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.kahanMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michele Graffeo, Giorgio Gubbiotti (2024). *Growth and Integrability of Some Birational Maps in Dimension Three*. DOI: [10.1007/s00023-023-01339-5](https://doi.org/10.1007/s00023-023-01339-5). URL: <https://arxiv.org/abs/2301.09129v2>.

*Commentary.*

The first three coordinates of X form x and its last coordinate is X 3. The matrix is X 3 times the identity minus twice the real step h, included in the complex numbers, times the polarised Nambu matrix. For the quadratic vector field f(x) = 4 Ax × Bx, Definition 2.1 of the KHK step (TeX lines 634–656) gives x′ − x = 2h(Ax × Bx′ + Ax′ × Bx). This matrix is the homogeneous form of the linear system for x′.

**Definition 1.3 (The homogeneous Nambu KHK lift).**

$$\forall \left(A: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(B: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(h: \mathbb{R}\right), \left(\forall \left(X: \operatorname{Fin}\left(4\right) \to \mathbb{C}\right), \left(\operatorname{kahan}\left(A, B, h, X\right) = \operatorname{Fin.snoc}\left(\operatorname{Matrix.mulVec}\left(\operatorname{Matrix.adjugate}\left(\operatorname{kahanMatrix}\left(A, B, h, X\right)\right), \left(\left(i: \operatorname{Fin}\left(3\right)\right) \mapsto \left(X\left(\operatorname{Fin.castSucc}\left(i\right)\right)\right)\right)\right), \operatorname{Matrix.det}\left(\operatorname{kahanMatrix}\left(A, B, h, X\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.kahan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michele Graffeo, Giorgio Gubbiotti (2024). *Growth and Integrability of Some Birational Maps in Dimension Three*. DOI: [10.1007/s00023-023-01339-5](https://doi.org/10.1007/s00023-023-01339-5). URL: <https://arxiv.org/abs/2301.09129v2>.

*Commentary.*

Apply the adjugate of the homogeneous KHK matrix to the first three coordinates, then append its determinant as the fourth coordinate. Fin.snoc performs this append. In the affine chart with X 3 = 1 and nonzero determinant, dividing by the last coordinate gives the KHK update. The polynomial lift is defined even when that determinant vanishes. It encodes the homogeneous Nambu KHK map introduced in Remark 7.7, TeX lines 3207–3208.

**Definition 1.4 (The standard cubic Cremona lift).**

$$\forall \left(X: \operatorname{Fin}\left(4\right) \to \mathbb{C}\right), \left(\operatorname{cremona}\left(X\right) = ![\left(\left(X\left(\left(1: \operatorname{Fin}\left(4\right)\right)\right)\right) \cdot \left(X\left(\left(2: \operatorname{Fin}\left(4\right)\right)\right)\right)\right) \cdot \left(X\left(\left(3: \operatorname{Fin}\left(4\right)\right)\right)\right), \left(\left(X\left(\left(0: \operatorname{Fin}\left(4\right)\right)\right)\right) \cdot \left(X\left(\left(2: \operatorname{Fin}\left(4\right)\right)\right)\right)\right) \cdot \left(X\left(\left(3: \operatorname{Fin}\left(4\right)\right)\right)\right), \left(\left(X\left(\left(0: \operatorname{Fin}\left(4\right)\right)\right)\right) \cdot \left(X\left(\left(1: \operatorname{Fin}\left(4\right)\right)\right)\right)\right) \cdot \left(X\left(\left(3: \operatorname{Fin}\left(4\right)\right)\right)\right), \left(\left(X\left(\left(0: \operatorname{Fin}\left(4\right)\right)\right)\right) \cdot \left(X\left(\left(1: \operatorname{Fin}\left(4\right)\right)\right)\right)\right) \cdot \left(X\left(\left(2: \operatorname{Fin}\left(4\right)\right)\right)\right)]\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.cremona` (`✓ std3`).

*Citation.* Michele Graffeo, Giorgio Gubbiotti (2024). *Growth and Integrability of Some Birational Maps in Dimension Three*. DOI: [10.1007/s00023-023-01339-5](https://doi.org/10.1007/s00023-023-01339-5). URL: <https://arxiv.org/abs/2301.09129v2>.

*Commentary.*

Each coordinate is the product of the other three coordinates. On the projective torus this is coordinatewise inversion, the standard Cremona transformation in equation (C3), TeX lines 169–176, specialised to projective dimension three. The four entries use indices zero through three.

**Definition 1.5 (Decomposition for every simple positive definite pencil).**

$$\operatorname{claim} = \left(\forall \left(A: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(B: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\left(\operatorname{Matrix.PosDef}\left(A\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.PosDef}\left(B\right)\right) \Rightarrow \left(\left(\forall \left(t: \mathbb{R}\right), \left(2 \le \operatorname{Matrix.rank}\left(B - \operatorname{HSMul.hSMul}\left(t, A\right)\right)\right)\right) \Rightarrow \left(\forall \left(h: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < h\right) \Rightarrow \left(\exists \left(l_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)\right), \left(\exists \left(l_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)\right), \left(\left(\operatorname{IsUnit}\left(\operatorname{Matrix.det}\left(l_{1}\right)\right)\right) \land \left(\left(\operatorname{IsUnit}\left(\operatorname{Matrix.det}\left(l_{2}\right)\right)\right) \land \left(\forall \left(X: \operatorname{Fin}\left(4\right) \to \mathbb{C}\right), \left(\operatorname{kahan}\left(A, B, h, X\right) = \operatorname{Matrix.mulVec}\left(l_{2}, \operatorname{cremona}\left(\operatorname{Matrix.mulVec}\left(l_{1}, X\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michele Graffeo, Giorgio Gubbiotti (2024). *Growth and Integrability of Some Birational Maps in Dimension Three*. DOI: [10.1007/s00023-023-01339-5](https://doi.org/10.1007/s00023-023-01339-5). URL: <https://arxiv.org/abs/2301.09129v2>.

*Commentary.*

For every pair of real positive definite matrices whose pencil B − tA has rank at least two for every real t, and every positive real h, two invertible complex four by four matrices factor the KHK lift through the cubic Cremona lift. Positive definiteness includes symmetry; the rank condition expresses distinct generalised eigenvalues. The identity holds for every complex homogeneous vector, including zero. This is the simple-pencil formulation of the conjecture in Remark 7.7 (TeX lines 3209–3214), extending the Euler-top factorisation of Lemma 2.6 (lines 1063–1101). Conjugation by a projectivity is absorbed into the two linear factors. Repeated eigenvalues, the eight-point base-locus criterion, and degree-growth classifications are outside the proposition.

**Theorem 1.6 (The Nambu KHK lift factors through Cremona).**

$$\forall \left(A: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\forall \left(B: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{R}\right)\right), \left(\left(\operatorname{Matrix.PosDef}\left(A\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.PosDef}\left(B\right)\right) \Rightarrow \left(\left(\forall \left(t: \mathbb{R}\right), \left(2 \le \operatorname{Matrix.rank}\left(B - \operatorname{HSMul.hSMul}\left(t, A\right)\right)\right)\right) \Rightarrow \left(\forall \left(h: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < h\right) \Rightarrow \left(\exists \left(l_{1}: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)\right), \left(\exists \left(l_{2}: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right)\right), \left(\left(\operatorname{IsUnit}\left(\operatorname{Matrix.det}\left(l_{1}\right)\right)\right) \land \left(\left(\operatorname{IsUnit}\left(\operatorname{Matrix.det}\left(l_{2}\right)\right)\right) \land \left(\forall \left(X: \operatorname{Fin}\left(4\right) \to \mathbb{C}\right), \left(\operatorname{kahan}\left(A, B, h, X\right) = \operatorname{Matrix.mulVec}\left(l_{2}, \operatorname{cremona}\left(\operatorname{Matrix.mulVec}\left(l_{1}, X\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.result` (`✓ std3`). ∎

*Resolves.* `Problems/graffeo-gubbiotti-2024-nambu-kahan-cremona-decomposition` (proved) by `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"graffeo-gubbiotti-2024-nambu-kahan-cremona-decomposition","declaration_gid":"D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michele Graffeo, Giorgio Gubbiotti (2024). *Growth and Integrability of Some Birational Maps in Dimension Three*. DOI: [10.1007/s00023-023-01339-5](https://doi.org/10.1007/s00023-023-01339-5). URL: <https://arxiv.org/abs/2301.09129v2>.

*Commentary.*

Begin with an Euler vector field with complex coefficients a₁, a₂, a₃. Its Jacobian at y has zero diagonal and off-diagonal entries a₁y₂, a₁y₁ in row zero, a₂y₂, a₂y₀ in row one, and a₃y₁, a₃y₀ in row two. Denote this matrix by J and the lift obtained from X 3 times the identity minus (h/2)J by Φ. For square roots α² = a₁, β² = a₂, γ² = a₃, form a matrix C whose rows are (−βγh, −αγh, αβh, −2), (βγh, −αγh, −αβh, −2), (−βγh, αγh, −αβh, −2), and (βγh, αγh, αβh, −2). Let G have diagonal entries one and every off-diagonal entry minus one. Expanding the four coordinates and using the square-root identities proves CΦ(X) = (−1/8)G cremona(CX). Expanding determinants gives det C = 32α²β²γ²h³ and det G = −16, so G is invertible.

Next normalise the real quadratic forms. Choose a positive definite symmetric square root L of A and put S = L⁻¹. Then SᵀAS = I. The real symmetric matrix SᵀBS has an orthogonal eigenvector matrix Q and real eigenvalues mu. With P = SQ, both P and its determinant are invertible, PᵀAP = I, and PᵀBP = diagonal mu. Multiplication by P and Pᵀ preserves rank, so diagonal(mu − t) has rank at least two for every real t. If two distinct indices had the same eigenvalue, taking t equal to it would leave at most one nonzero diagonal entry. The diagonal-rank formula would give rank at most one, a contradiction. Thus the three eigenvalues are distinct.

Include P in the complex matrices and extend it by a final identity coordinate to an invertible four by four matrix R. For any complex three by three matrix D, direct expansion gives (Du) × (Dv) = adj(D)ᵀ(u × v). For invertible D the adjugate is det(D)D⁻¹; this also proves that adjugates commute with conjugation and yields (D⁻ᵀu) × (D⁻ᵀv) = det(D)⁻¹D(u × v). The column definition of the polarised Nambu matrix gives its action on every v as Ax × Bv + Av × Bx.

Set a₁ = 4((mu 2 : ℂ) − (mu 1 : ℂ))/(det P : ℂ), a₂ = 4((mu 0 : ℂ) − (mu 2 : ℂ))/(det P : ℂ), and a₃ = 4((mu 1 : ℂ) − (mu 0 : ℂ))/(det P : ℂ). The two normalised-form identities express the transformed A and B through the inverse transpose of P and the diagonal matrix of mu. The cross-product identity then identifies the transformed polarised matrix with one quarter of J. Consequently the Nambu KHK matrix at RZ is conjugate by P to the Euler KHK matrix at Z: the factor 2h times one quarter becomes h/2. Adjugate conjugation and determinant invariance, together with the appended last coordinate, give kahan A B h (RZ) = RΦ(Z) exactly.

Finally fix A, B and positive h satisfying the proposition. The distinct eigenvalues and nonzero determinant of P make all three coefficients a₁, a₂, a₃ nonzero. Algebraic closure of ℂ provides α, β, γ with the required squares. Include h in ℂ; it is nonzero because h is positive. The determinant formula therefore makes C invertible. Set U = CR⁻¹, l₁ = U and l₂ = (−1/8)U⁻¹G. Both determinants are nonzero: this follows from those of C, R and G and the nonzero scalar −1/8. For each X, substitute Z = R⁻¹X into the change-of-coordinates identity and the Euler identity. Cancelling R⁻¹R gives U kahan A B h X = (−1/8)G cremona(UX). Multiplication by U⁻¹ gives the asserted factorisation with l₁ and l₂. All identities are polynomial identities in X, so no exclusion of a zero coordinate or a singular KHK matrix is needed.

## References

- Truth anchor: `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.claim`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.cremona`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.kahan`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.kahanMatrix`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.nambuLinearPart`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition.result`
- Dependency: [D5/S3/Observer/Hankel/PositiveGramianBalancing](../../Observer/Hankel/PositiveGramianBalancing.md)
