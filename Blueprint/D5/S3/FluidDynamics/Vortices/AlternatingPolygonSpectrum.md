# Alternating vortex polygon spectrum

## Abstract

The alternating unit polygon has exactly m minus two distinct pairs of nonzero real eigenvalues.

**Definition 1.1 (Alternating charge).**

$$\forall (N: \mathbb{N}), (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.charge}\left(N, j\right) = (-((1: \mathbb{R})))^{(\operatorname{Fin.val}\left(j\right)) + (2)}))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.charge` (`✓ std3`).

*Citation.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The zero-based label j represents the source's label j+1, so its charge is minus one to the power j.val+2. This is the alternating pattern of Section 4.1, arXiv:1306.1545v2, TeX lines 506–507.

**Definition 1.2 (The Cartesian point-vortex field).**

$$\forall (N: \mathbb{N}), (\forall (z: (\operatorname{Sum}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right)\right)) \to (\mathbb{R})), (\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.field}\left(N, z\right) = \lambda (p: \operatorname{Sum}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right)\right)) \mapsto (\operatorname{Sum.elim}\left(\lambda (j: \operatorname{Fin}\left(N\right)) \mapsto ((((-(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.charge}\left(N, j\right))) \cdot (\frac{(1: \mathbb{R})}{2})) \cdot (z\left(\operatorname{Sum.inr}\left(j\right)\right))) - (\sum_{k: \operatorname{Fin}\left(N\right)} (\operatorname{ite}\left(k = j, (0: \mathbb{R}), \frac{(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.charge}\left(N, k\right)) \cdot ((z\left(\operatorname{Sum.inr}\left(j\right)\right)) - (z\left(\operatorname{Sum.inr}\left(k\right)\right)))}{(((z\left(\operatorname{Sum.inl}\left(j\right)\right)) - (z\left(\operatorname{Sum.inl}\left(k\right)\right)))^{2}) + (((z\left(\operatorname{Sum.inr}\left(j\right)\right)) - (z\left(\operatorname{Sum.inr}\left(k\right)\right)))^{2})}\right)))), \lambda (j: \operatorname{Fin}\left(N\right)) \mapsto ((((\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.charge}\left(N, j\right)) \cdot (\frac{(1: \mathbb{R})}{2})) \cdot (z\left(\operatorname{Sum.inl}\left(j\right)\right))) + (\sum_{k: \operatorname{Fin}\left(N\right)} (\operatorname{ite}\left(k = j, (0: \mathbb{R}), \frac{(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.charge}\left(N, k\right)) \cdot ((z\left(\operatorname{Sum.inl}\left(j\right)\right)) - (z\left(\operatorname{Sum.inl}\left(k\right)\right)))}{(((z\left(\operatorname{Sum.inl}\left(j\right)\right)) - (z\left(\operatorname{Sum.inl}\left(k\right)\right)))^{2}) + (((z\left(\operatorname{Sum.inr}\left(j\right)\right)) - (z\left(\operatorname{Sum.inr}\left(k\right)\right)))^{2})}\right)))), p\right))))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.field` (`✓ std3`).

*Citation.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The two summands of Fin N ⊕ Fin N label the x and y coordinates. The field is Equations (1)–(2) with b=2 and Ω=1/2 (TeX lines 168–176 and 526–532). Self-interactions are set to zero. Real division defines a total function, while at distinct polygon vertices all interaction denominators are nonzero.

**Definition 1.3 (The regular unit polygon).**

$$\forall (N: \mathbb{N}), (\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.polygon}\left(N\right) = \lambda (p: \operatorname{Sum}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right)\right)) \mapsto (\operatorname{Sum.elim}\left(\lambda (j: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{Real.cos}\left(\frac{((2) \cdot (\operatorname{Real.pi})) \cdot (((\operatorname{Fin.val}\left(j\right): \mathbb{R})) + (1))}{(N: \mathbb{R})}\right)), \lambda (j: \operatorname{Fin}\left(N\right)) \mapsto (\operatorname{Real.sin}\left(\frac{((2) \cdot (\operatorname{Real.pi})) \cdot (((\operatorname{Fin.val}\left(j\right): \mathbb{R})) + (1))}{(N: \mathbb{R})}\right)), p\right)))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.polygon` (`✓ std3`).

*Citation.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The coordinates are the cosine and sine of 2π(j.val+1)/N. This is the source's order z₁=exp(2πi/N), through zN=1 (TeX line 515). The source sets Ω=1/2 for the even polygon equilibrium (TeX lines 524–532).

**Definition 1.4 (The Cartesian linearization).**

$$\forall (N: \mathbb{N}), (\forall (p: \operatorname{Sum}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right)\right)), (\forall (q: \operatorname{Sum}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right)\right)), (\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian}\left(N, p, q\right) = \operatorname{deriv}\left(\lambda (t: \mathbb{R}) \mapsto (\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.field}\left(N, (\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.polygon}\left(N\right)) + ((t) \cdot (\operatorname{Pi.single}\left(q, (1: \mathbb{R})\right))), p\right)), (0: \mathbb{R})\right))))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.jacobian` (`✓ std3`).

*Citation.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The entry in row p and column q is the derivative at zero of the pth field coordinate along the affine line through the polygon in direction Pi.single q 1. It is the Cartesian Jacobian of the source's model; the source examines its linearization in polar coordinates (TeX lines 543–550).

**Definition 1.5 (The distinct-real-pair conjecture).**

$$\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.claim} = (\forall (m: \mathbb{N}), ((3 \le m) \Rightarrow ((\forall (x: \mathbb{R}), ((\operatorname{Polynomial.IsRoot}\left(\operatorname{Matrix.charpoly}\left(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian}\left((2) \cdot (m)\right)\right), x\right)) \Rightarrow (\operatorname{Polynomial.IsRoot}\left(\operatorname{Matrix.charpoly}\left(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian}\left((2) \cdot (m)\right)\right), -(x)\right)))) \land (\operatorname{Set.ncard}\left(\{(x: \mathbb{R}) \mid (x \ne (0: \mathbb{R})) \land (\operatorname{Polynomial.IsRoot}\left(\operatorname{Matrix.charpoly}\left(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian}\left((2) \cdot (m)\right)\right), x\right))\}\right) = (2) \cdot (((m) - (2): \mathbb{N}))))))$$

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Conjecture 4.4 asks for N/2−2 distinct pairs of real eigenvalues of the alternating N-gon (TeX lines 627–633). For N=2m and m≥3, this proposition asserts sign symmetry of every real characteristic root and cardinality 2(m−2) for the set of nonzero real roots. Zero and algebraic multiplicities are excluded from the count. The source proposes this assertion as a conjecture.

**Theorem 1.6 (Exactly m minus two real pairs).**

$$\forall (m: \mathbb{N}), ((3 \le m) \Rightarrow ((\forall (x: \mathbb{R}), ((\operatorname{Polynomial.IsRoot}\left(\operatorname{Matrix.charpoly}\left(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian}\left((2) \cdot (m)\right)\right), x\right)) \Rightarrow (\operatorname{Polynomial.IsRoot}\left(\operatorname{Matrix.charpoly}\left(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian}\left((2) \cdot (m)\right)\right), -(x)\right)))) \land (\operatorname{Set.ncard}\left(\{(x: \mathbb{R}) \mid (x \ne (0: \mathbb{R})) \land (\operatorname{Polynomial.IsRoot}\left(\operatorname{Matrix.charpoly}\left(\operatorname{D5.S3.FluidDynamics.Vortices.AlternatingPolygonSpectrum.jacobian}\left((2) \cdot (m)\right)\right), x\right))\}\right) = (2) \cdot (((m) - (2): \mathbb{N})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.result` (`✓ std3`). ∎

*Resolves.* `Problems/barry-kevrekidis-2013-alternating-vortex-polygon-spectrum` (proved) by `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barry-kevrekidis-2013-alternating-vortex-polygon-spectrum","declaration_gid":"D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

First prove distinctness of the prospective squared positive roots. For natural numbers 2≤k<l<m, put s=k+l and f(a)=(m−a)²(a²−2), using real arithmetic. Then f(k)−f(l)=(k−l)Q(m), where Q(t)=st²−2(k²+kl+l²−2)t+s(k²+l²−2). One has Q(l)=−(l−k)(k²−2)<0. Writing u=k−2 and v=l−k−1 gives Q(s−1)=−(2u²+2uv+4u+v+1)<0. If m<s, use (k−1)Q(m)=(s−1−m)Q(l)+(m−l)Q(s−1)−s(k−1)(m−l)(s−1−m)<0. If m≥s, put h=m−s≥0; then Q(m)=2s+(2kl+4)h+sh²>0. Thus Q(m)≠0 and f(k)≠f(l).

The squared distance between polygon vertices j and k is 4sin²(π(j.val−k.val)/N). For j≠k the angle lies strictly between −π and π and is nonzero, so this distance is nonzero. Differentiate the field along z(t)=polygon N+t·Pi.single q 1, using the quotient rule and finite-sum differentiation. For a squared distance d and its directional derivative e, each quotient derivative has numerator equal to the directional coordinate difference times d minus the coordinate difference times e, and denominator d². The self-interaction derivative is zero.

For N=2m the reflection k↦j+j−k preserves the alternating charge. For either Cartesian coordinate v, the two reflected terms (v(j)−v(k))/d(j,k) and (v(j)−v(j+j−k))/d(j,j+j−k) sum to v(j). The total alternating charge is zero, so the interaction sum equals −charge N j·v(j)/2. This cancels the precession term in each field coordinate, proving that the polygon is an equilibrium.

At vertex j use the radial and tangential columns (xj,yj) and (−yj,xj). The resulting matrix has blocks diag(x), −diag(y), diag(y), diag(x), and its product with its transpose is the identity by xj²+yj²=1. Conjugating the differentiated Cartesian matrix by it gives zero diagonal blocks. At distinct vertices both off-diagonal block entries are −charge N k·weights m j k. On the diagonal the upper-right entry is w=Σk charge N k·weights m j k and the lower-left entry is charge N j+w; the equilibrium identities give these simplifications. The alternating weight sum yields w=charge N j·diagonalWeight m. Thus the four blocks are 0, blockB m, blockC m, 0.

For nonzero real x, similarity preserves the characteristic polynomial. Apply the Schur determinant formula to xI, −blockB m, −blockC m, xI, using the inverse x⁻¹I of xI. Scale the Schur complement by x and cancel nonzero determinants. Then x is a characteristic root exactly when det(x²I−blockC m·blockB m)=0. The product_spectrum identity factors this determinant into the product of x²−gamma m k over k in ZMod (2m). Its common Fourier basis uses the inverse-squared-chord Fourier values and the shift by m induced by alternating signs.

For a vanishing factor put r=min(k.val,2m−k.val), so 0≤r≤m and x²=(m−r)²(r²−2)/4. Since x≠0, its square is positive. The cases r=0 and r=1 make the right side nonpositive, and r=m makes it zero. Therefore 2≤r<m. Conversely, every natural r in this interval gives a residue with least representative r and hence this factor. The nonzero real roots are exactly ±(m−r)√(r²−2)/2 for 2≤r<m.

The positive expression is strictly positive and has the required square. The initial argument makes its values distinct for distinct r. Negation is injective, and its image is disjoint from the positive image. The natural interval from 2 to m−1 has m−2 elements, so the union has 2(m−2) elements. The determinant condition depends only on x², giving sign symmetry for nonzero roots; zero is fixed by negation. Both conclusions hold for every m≥3.

This concerns the point-vortex field with b=2, Ω=1/2 and unit radius. It asserts no odd-polygon, other-charge, eigenvector, nonlinear-stability or Gross–Pitaevskii stability conclusion.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.charge`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.claim`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.field`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.jacobian`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.polygon`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.result`
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/CircleGraphCharts](../../ConceptDynamics/ObservationTopology/CircleGraphCharts.md)
- Dependency: [D5/S3/FluidDynamics/Vortices/InverseChordCirculant](InverseChordCirculant.md)
