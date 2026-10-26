# LatticeThetaTransformation

## Abstract

For actual LatticeData D, assume its real Gram matrix is positive definite, its integral Gram determinant is a unit, and its rank equals m+m for a natural m. For every complex tau with positive imaginary part, the ordinary charge theta terms have summable norms and latticeTheta D (-1/tau)=(-i tau)^m latticeTheta D tau. The integer Gram matrix acts bijectively on charges, with its integral matrix inverse providing the inverse map. This reindexes the inverse-form theta series; positivity and integral unimodularity give determinant one. Rank zero is included. This theta identity does not identify any operator trace or oscillator factor.

**Theorem 1.1 (Integer inverse-form reindexing).**

$$\forall r \in \mathbb{N},\; \forall G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{Z}\right),\; \left(\operatorname{PosDef}\left(\operatorname{map}\left(G, \operatorname{IntCastRingHom}\left(\mathbb{R}\right)\right)\right) \land \operatorname{IsUnit}\left(\operatorname{det}\left(G\right)\right)\right) \Rightarrow \left(\forall tau \in \mathbb{C},\; \operatorname{theta}\left(\operatorname{map}\left(G, \operatorname{IntCastRingHom}\left(\mathbb{R}\right)\right)^{-1}, tau\right) = \operatorname{theta}\left(\operatorname{map}\left(G, \operatorname{IntCastRingHom}\left(\mathbb{R}\right)\right), tau\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/LatticeThetaTransformation.theta_inverse_integer_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural rank r, integer matrix G whose real extension is positive definite, unit integral determinant and complex tau, the theta series of the inverse real Gram equals the theta series of the real Gram. Multiplication by G is a bijection of the full integer coordinate space, with inverse multiplication by the integral matrix inverse. The quadratic identity follows from actual matrix inverse cancellation. Evenness and positive rank are not required for this reindexing.

**Definition 1.2 (The ordinary integral-charge theta series).**

$$\forall D \in LatticeData,\; \forall tau \in \mathbb{C},\; \operatorname{latticeTheta}\left(D, tau\right) = \operatorname{tsum}\left((a:\operatorname{Charge}\left(D\right) \mapsto \operatorname{exp}\left(\pi \cdot \operatorname{Complex}.\operatorname{I} \cdot tau \cdot (\operatorname{bilinear}\left(D, a, a\right):\mathbb{C})\right))\right)$$

*Formalization.* `D5/S3/Arith/Lattices/LatticeThetaTransformation.latticeTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For actual LatticeData D, latticeTheta D tau sums exp(pi i tau bilinear_D(a,a)) over every integer charge a. This is the ordinary charge sum.

**Theorem 1.3 (The even-unimodular lattice S law).**

$$\forall D \in LatticeData,\; \left(\operatorname{PosDef}\left(\operatorname{map}\left(D.G, \operatorname{IntCastRingHom}\left(\mathbb{R}\right)\right)\right) \land \operatorname{IsUnit}\left(\operatorname{det}\left(D.G\right)\right)\right) \Rightarrow \left(\forall m \in \mathbb{N},\; \operatorname{rank}\left(D\right) = m + m \Rightarrow \left(\forall tau \in \mathbb{C},\; 0 < \operatorname{im}\left(tau\right) \Rightarrow \left(\operatorname{Summable}\left((a:\operatorname{Charge}\left(D\right) \mapsto \left\lVert \operatorname{exp}\left(\pi \cdot \operatorname{Complex}.\operatorname{I} \cdot tau \cdot (\operatorname{bilinear}\left(D, a, a\right):\mathbb{C})\right) \right\rVert)\right) \land \operatorname{latticeTheta}\left(D, \frac{-1}{tau}\right) = \left(-\operatorname{Complex}.\operatorname{I} \cdot tau\right)^{m} \cdot \operatorname{latticeTheta}\left(D, tau\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/LatticeThetaTransformation.lattice_theta_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For actual LatticeData D, assume its real Gram matrix is positive definite, its integral Gram determinant is a unit, and its rank equals m+m for a natural m. For every complex tau with positive imaginary part, the ordinary charge theta terms have summable norms and latticeTheta D (-1/tau)=(-i tau)^m latticeTheta D tau. The integer Gram matrix acts bijectively on charges, with its integral matrix inverse providing the inverse map. This reindexes the inverse-form theta series; positivity and integral unimodularity give determinant one. Rank zero is included. This theta identity does not identify any operator trace or oscillator factor.

## References

- Truth anchor: `D5/S3/Arith/Lattices/LatticeThetaTransformation.latticeTheta`
- Truth anchor: `D5/S3/Arith/Lattices/LatticeThetaTransformation.lattice_theta_S`
- Truth anchor: `D5/S3/Arith/Lattices/LatticeThetaTransformation.theta_inverse_integer_reindex`
- Dependency: [D5/S3/Fourier/MatrixGaussianTheta](../../Fourier/MatrixGaussianTheta.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality](../../VertexAlgebra/LatticeGeneratingFieldLocality.md)
