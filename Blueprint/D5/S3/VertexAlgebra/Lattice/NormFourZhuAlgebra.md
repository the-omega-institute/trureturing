# Actual Norm-Four Zhu Algebra and Monic Cubic Presentation

## Abstract

Actual Norm-Four Zhu Algebra and Monic Cubic Presentation.

**Definition 1.1 (Actual descended star product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientProduct`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every lattice D with invertible determinant, norm-four charge a and complex s with s squared equal to one, the product on the original additive quotient S/O descends from the actual bilinear star on S. On a homogeneous left state of weight n, star is the full sum of binomial(n,j) times u_(j-1)v for j from zero through n. Canonical finite homogeneous expansion extends it to every left state.

**Definition 1.2 (Actual commutative quotient ring).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientRing`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientRing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D with invertible determinant, norm-four a and s squared equal to one, this commutative ring reuses the original quotient addition, the actual descended star product and the actual vacuum class as unit.

**Definition 1.3 (Compatible complex algebra).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D with invertible determinant, norm-four a and s squared equal to one, the existing complex module on S/O is compatible with the actual quotient ring. Complex constants map to scalar multiples of the vacuum class.

**Theorem 1.4 (Actual star algebra and dimension three).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_algebra`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integral symmetric even-diagonal lattice D with IsUnit D.G.det, charge a with B(a,a)=4, and complex s with s squared equal to one, the original literal Zhu quotient has its actual star algebra structure. The class of star(u,v) equals the product of the classes of u and v for all u,v in S. The quotient is finite dimensional of dimension exactly three. Its actual axis class x satisfies x(x-1/16)(x-1/2)=0, where the constants are supplied by the compatible complex algebra.

**Definition 1.5 (Monic axis polynomial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.zhuPolynomial`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.zhuPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex polynomial is P=X(X-C(1/16))(X-C(1/2)).

**Theorem 1.6 (Actual monic cubic presentation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_presentation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_presentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite integral symmetric even-diagonal lattice D with IsUnit D.G.det, charge a with B(a,a)=4, and complex s with s squared equal to one, P is monic and there exists a complex algebra equivalence from AdjoinRoot(P) to the original literal Zhu quotient with its actual star product. The equivalence maps the adjoined root to the actual axis class x. That class also satisfies 64 x cubed minus 36 x squared plus 2 x equals zero, using the original complex scalar action. There is no rank-24 hypothesis.

Actual word grading gives a unique finite homogeneous expansion. Mixed ambient Sugawara and axis commutators identify each word grade with its ambient source energy. The theta-fixed source and mode closure apply to the whole descendant space. Actual energy covariance makes high physical modes vanish on the complete first oscillator grade, and preserves that grade under zero modes.

The full production residue law proves that the original literal O annihilates this actual first grade and that star acts by composition. The circle specialization uses both ordered families; the star specialization retains the unique surviving first-family term and annihilates the complete second family. Every fused result grade is shown nonnegative before conversion to a natural number.

The general actual multiplicity equations imply rank at least two and positive dimensions of the zero, one-sixteenth and one-half eigenspaces. Their scalar readouts separate the images of the same three representatives: identity, the actual axis zero mode L, and L squared plus 2L. Actual filtered spanning then proves that the kernel of the actual action is exactly literal O. Both argument kernels of star follow. The descended faithful action proves associativity, the vacuum unit and commutativity.

The additive finite-dimensional upper bound is consumed from NormFourZhuFinite; the three actual spectral fibers give the reverse bound. The actual first-grade polynomial supplies the cubic relation. Representative multiplication and the circle relation identify the second representative class with x squared plus 2x. These classes make the AdjoinRoot map surjective; equality of the two dimensions makes it injective.

This realizes the classical Zhu construction and the central-charge-one-half Virasoro cubic presentation in the actual lattice carrier. It adds no assumed basis, ideal, associative product, abstract representation, positive form or rank specialization. Rationality, fusion, a full Monster construction, analytic CFT and string realization are not established here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_algebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_presentation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientProduct`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientRing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.zhuPolynomial`
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure](../GroundRightCurrentTransport/FirstSourceClosure.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualEnergyCovariance](../HalfFock/ActualEnergyCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/NormFourFirstGradeSpectrum](../HalfFock/NormFourFirstGradeSpectrum.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourCosetVirasoro](NormFourCosetVirasoro.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite](NormFourZhuFinite.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling](../LatticeHalfFockPhysicalRescaling.md)
