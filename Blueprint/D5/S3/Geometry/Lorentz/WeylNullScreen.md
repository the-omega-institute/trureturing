# Weyl curvature from future null screens

## Abstract

Five distinct future null screens determine four-dimensional Weyl curvature, with exact rank for every finite family.

How many future null directions determine Weyl curvature at a point? Five distinct directions suffice. For N distinct directions the rank is min(10, 2N), and every family with at most four rays has a nonzero curvature witness in its kernel.

**Theorem 1.1 (Exact rank and kernel dimension).**

$$\forall N \in \mathbb{N},\; \forall ray \in \operatorname{Fin}\left(N\right) \to \operatorname{FutureNullRay},\; (\operatorname{Injective}\left(ray\right) \implies (\operatorname{finrank}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{nullTidalSample}\left(ray\right)\right)\right) = \operatorname{min}\left(10, 2 \cdot N\right) \land \operatorname{finrank}\left(\mathbb{R}, \operatorname{ker}\left(\operatorname{nullTidalSample}\left(ray\right)\right)\right) = \operatorname{max}\left(0, 10 - 2 \cdot N\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_sampling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linear map samples the complex Weyl tide at each ray, with its real and imaginary parts encoding the two independent transverse components. At finite rays the contraction evaluates the degree-at-most-four polynomial. At infinity it reads the coefficient of z⁴. For N at most five, Lagrange interpolation assigns arbitrary values at the finite nodes. If the family contains infinity, subtract the prescribed leading term and interpolate the finite residual values in degree at most three. On any five rays the interpolation map is surjective between complex spaces of dimension five, so it is injective. For a larger family, restriction to five rays then gives injectivity. The codomain has real dimension 2N. Rank–nullity gives the stated kernel dimension, including an empty family.

**Definition 1.2 (Reconstruction from any five rays).**

Lean statement: `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_five`

*Formalization.* `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_five` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map takes the five tidal samples. The inverse interpolates the quartic from the samples in the same chart, then applies the inverse Weyl-to-quartic map. Agreement at those five rays proves the two inverse laws.

**Theorem 1.3 (Five vanishing tides force zero Weyl curvature).**

$$\forall ray \in \operatorname{Fin}\left(5\right) \to \operatorname{FutureNullRay},\; (\operatorname{Injective}\left(ray\right) \implies (\forall C \in \operatorname{Weyl4},\; (\operatorname{nullTidalSample}\left(ray, C\right) = 0 \iff C = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Z. Petrov (2000). *The Classification of Spaces Defining Gravitational Fields*. DOI: [10.1023/A:1001910908054](https://doi.org/10.1023/A:1001910908054). URL: <https://link.springer.com/article/10.1023/A:1001910908054>.

*Commentary.*

The five-ray reconstruction implies that a Weyl matrix vanishes exactly when its five sampled tides vanish. A nonzero Weyl tensor therefore has at most four distinct principal null directions, the rays on which its trace-free tide vanishes.

**Theorem 1.4 (A nonzero witness for at most four rays).**

$$\forall N \in \mathbb{N},\; \forall ray \in \operatorname{Fin}\left(N\right) \to \operatorname{FutureNullRay},\; ((N \leq 4) \implies (\operatorname{nullTidalSample}\left(ray, \operatorname{vanishingWeyl}\left(ray\right)\right) = 0 \land (\operatorname{vanishingWeyl}\left(ray\right) \neq 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_vanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each finite node z in the sampled family, include a factor X−z and multiply the factors. The polynomial is monic, so its inverse Weyl image is nonzero. If infinity is sampled, there are at most three finite factors, and the leading quartic coefficient vanishes. Repetitions are allowed. The empty family uses the constant polynomial 1.

**Theorem 1.5 (One complex component encodes the Weyl tide).**

$$\forall C \in \operatorname{Weyl4},\; \forall r \in \operatorname{FutureNullRay},\; \operatorname{complexTide}\left(\operatorname{val}\left(C\right), r\right) = 2 \cdot (\operatorname{tidal}\left(\operatorname{val}\left(C\right), \operatorname{nullGenerator}\left(r\right), \operatorname{screenFrame}\left(r, 0\right), \operatorname{screenFrame}\left(r, 0\right)\right) + \operatorname{I} \cdot \operatorname{tidal}\left(\operatorname{val}\left(C\right), \operatorname{nullGenerator}\left(r\right), \operatorname{screenFrame}\left(r, 0\right), \operatorname{screenFrame}\left(r, 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.complexTide_weyl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real screen tidal matrix is symmetric, and its trace is the Ricci contraction on the null generator. For Weyl curvature this trace vanishes. Expanding the complex contraction on the real and imaginary parts of the screen vector yields twice the first diagonal entry plus twice i times the off-diagonal entry.

**Theorem 1.6 (Quartic evaluation is the complex screen contraction).**

$$\forall C \in \operatorname{Weyl4},\; \forall r \in \operatorname{FutureNullRay},\; \operatorname{quarticEval}\left(r, \operatorname{weylQuarticEquiv}\left(C\right)\right) = \operatorname{complexTide}\left(\operatorname{val}\left(C\right), r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.weylQuarticEquiv_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a finite ray the oriented bivector of the complex screen vector and null generator has blocks x and −ix, where x = (z²−1, −i(z²+1), 2z). The Weyl block matrix then reduces the contraction to 2 xᵀ(E−iM)x. Its expansion gives the quartic. The screen contracted at infinity gives exactly the fourth-degree coefficient.

**Theorem 1.7 (The trace-free null tide is the Weyl tide).**

$$\forall R \in \operatorname{AlgebraicCurvature4},\; \forall r \in \operatorname{FutureNullRay},\; \forall a \in \operatorname{Fin}\left(2\right),\; \forall b \in \operatorname{Fin}\left(2\right),\; (\operatorname{T}\left(R, r, a, b\right) = \operatorname{T}\left(\operatorname{W}\left(R\right), r, a, b\right) + \frac{\operatorname{delta}\left(a, b\right) \cdot \operatorname{Ric}\left(R, r\right)}{2} \land \operatorname{T}\left(R, r, a, b\right) - \frac{\operatorname{delta}\left(a, b\right) \cdot (\operatorname{T}\left(R, r, 0, 0\right) + \operatorname{T}\left(R, r, 1, 1\right))}{2} = \operatorname{T}\left(\operatorname{W}\left(R\right), r, a, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.null_tidal_ricci_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each ordered pair of frame vectors, evaluate the Ricci decomposition on their wedges with the null generator k. The Kulkarni–Nomizu terms containing the squared norm of k or its pairing with either frame vector vanish. The scalar curvature term also vanishes because g(k,k) is zero. In the displayed identity, T(Q,r,a,b) contracts curvature Q with the chosen generator and frame at r. W(R) is the Weyl projection of R, Ric(R,r) evaluates the Ricci tensor of R on (k,k), and delta is the frame metric. Subtracting half the screen trace on the diagonal leaves the Weyl tide.

**Definition 1.8 (The Ricci and Weyl decomposition).**

Lean statement: `D5/S3/Geometry/Lorentz/WeylNullScreen.curvature_ricci_split`

*Formalization.* `D5/S3/Geometry/Lorentz/WeylNullScreen.curvature_ricci_split` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bivector order is (01, 02, 03, 23, 31, 12), with metric diag(−1, 1, 1, 1). The symmetric pair matrix satisfies the Bianchi equation tr(WC) = 0, where W exchanges the electric and spatial blocks. This trace is 2(C₀₁,₂₃ + C₀₂,₃₁ + C₀₃,₁₂). Ricci contraction sums the components R(a,b,a,d) against the diagonal metric, with b and d free. With S = Ric − r g/4 and r the Lorentzian trace of Ric, the inverse sends (C, S, r) to C + (g ⊙ S)/2 + r(g ⊙ g)/24. The Kulkarni–Nomizu contraction is Ric(g ⊙ h) = 2h + tr_g(h)g. Hence the second term has Ricci S and the scalar term has Ricci rg/4.

**Definition 1.9 (Electric and magnetic coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_electric_magnetic_equiv`

*Formalization.* `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_electric_magnetic_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the oriented pair basis, write the symmetric curvature matrix in electric, mixed and spatial blocks E, M and N. Ric₀₀ = tr E. The time–space Ricci entries are the skew differences of M. The spatial block of Ricci is −E + tr(N)Id − N. Vanishing Ricci forces tr E = 0, M symmetric and N = −E. The Bianchi equation is tr M = 0. Conversely every pair of real symmetric traceless three-by-three matrices E and M gives the Weyl matrix [[E, M], [M, −E]].

**Theorem 1.10 (Twenty algebraic curvature coordinates).**

$$\operatorname{finrank}\left(\mathbb{R}, \operatorname{AlgebraicCurvature4}\right) = 20$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.finrank_algebraicCurvature4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split gives real dimension 20 = 10 + 9 + 1.

**Theorem 1.11 (Ten real Weyl coordinates).**

$$\operatorname{finrank}\left(\mathbb{R}, \operatorname{Weyl4}\right) = 10$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.finrank_weyl4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Five complex coordinates give real dimension ten.

**Theorem 1.12 (Nine trace-free Ricci coordinates).**

$$\operatorname{finrank}\left(\mathbb{R}, \operatorname{TracelessRicci4}\right) = 9$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.finrank_tracelessRicci4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six off-diagonal and three independent diagonal entries determine a symmetric trace-free Ricci form. The Lorentzian trace equation solves for its remaining diagonal entry.

**Definition 1.13 (Weyl curvature and quartic coefficients).**

Lean statement: `D5/S3/Geometry/Lorentz/WeylNullScreen.weylQuarticEquiv`

*Formalization.* `D5/S3/Geometry/Lorentz/WeylNullScreen.weylQuarticEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Z. Petrov (2000). *The Classification of Spaces Defining Gravitational Fields*. DOI: [10.1023/A:1001910908054](https://doi.org/10.1023/A:1001910908054). URL: <https://link.springer.com/article/10.1023/A:1001910908054>.

*Commentary.*

Use A = E − iM to give Weyl coordinates their complex scalar multiplication. For A₁₁ = a, A₂₂ = b, A₁₂ = c, A₁₃ = d, A₂₃ = e and A₃₃ = −a−b, the coefficients in ascending order are 2(a−b)+4ic, −8d−8ie, −12(a+b), 8d−8ie and 2(a−b)−4ic. Their first and last entries recover a−b and c, the middle entry recovers a+b, and the two odd entries recover d and e. The inverse takes the real part of A for E and the negative imaginary part for M.

**Theorem 1.14 (Unique positive rescaling).**

$$\forall v \in \operatorname{Fin}\left(4\right) \to \mathbb{R},\; ((0 < v\left(0\right)) \implies (\operatorname{minkowski}\left(v, v\right) = 0 \implies \exists! (p: (\mathbb{R} \times \operatorname{FutureNullRay})), ((0 < \operatorname{fst}\left(p\right)) \land v = (\operatorname{fst}\left(p\right) \cdot \operatorname{nullGenerator}\left(\operatorname{snd}\left(p\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.future_null_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A future null vector has positive time coordinate and zero Minkowski squared norm. If its time plus third spatial coordinate is zero, nullity forces the first two spatial coordinates to vanish. The vector lies on the ray at infinity with positive scale given by its time coordinate. Otherwise the sum is positive, the scale is half the sum, and z is the first spatial coordinate plus i times the second, divided by the sum.

**Theorem 1.15 (The chart generators are future null).**

$$\forall r \in \operatorname{FutureNullRay},\; ((0 < \operatorname{nullGenerator}\left(r\right)\left(0\right)) \land \operatorname{minkowski}\left(\operatorname{nullGenerator}\left(r\right), \operatorname{nullGenerator}\left(r\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.nullGenerator_future` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite generator is (1+|z|², 2 Re z, 2 Im z, 1−|z|²), and the generator at infinity is (1, 0, 0, −1). Each has positive time coordinate and zero Minkowski squared norm.

**Theorem 1.16 (The transverse frame is orthonormal).**

$$\forall r \in \operatorname{FutureNullRay},\; ((\forall a \in \operatorname{Fin}\left(2\right),\; \operatorname{minkowski}\left(\operatorname{screenFrame}\left(r, a\right), \operatorname{nullGenerator}\left(r\right)\right) = 0) \land (\forall a \in \operatorname{Fin}\left(2\right),\; \forall b \in \operatorname{Fin}\left(2\right),\; \operatorname{minkowski}\left(\operatorname{screenFrame}\left(r, a\right), \operatorname{screenFrame}\left(r, b\right)\right) = \operatorname{delta}\left(a, b\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/WeylNullScreen.screenFrame_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite complex screen vector is (z, 1, i, −z), and the vector at infinity is (0, 1, −i, 0). The chosen real frame consists of its real and imaginary parts. Both are orthogonal to the corresponding null generator and have unit norm and zero mutual inner product.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.complexTide_weyl`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.curvature_ricci_split`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.finrank_algebraicCurvature4`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.finrank_tracelessRicci4`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.finrank_weyl4`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.future_null_ray`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.nullGenerator_future`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.null_tidal_ricci_invariance`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.screenFrame_spec`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.weylQuarticEquiv`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.weylQuarticEquiv_eval`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_electric_magnetic_equiv`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_five`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_sampling`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_vanishing`
- Truth anchor: `D5/S3/Geometry/Lorentz/WeylNullScreen.weyl_null_screen_zero`
