# Completeness of the original even cosines

## Abstract

Fourier normalization and cosine completeness for the original complex AE-even Lebesgue window sector.

WindowL2(a) is complex L2 with physical Lebesgue measure on Ioc(-a,a]. originalEven(a) was independently defined by AE reflection invariance of the whole-line indicator zero extension. The analytic comparisons and completeness theorems below require a>0. Fourier indices are integers, cosine indices are natural numbers, and the functions and coefficients remain complex.

**Definition 1.1 (Unnormalized physical Fourier moment).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.moment`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

character(a,k,x) is Mathlib's Fourier character at the class of x in AddCircle(2*a). moment(a,u,k) integrates character(a,-k,x) times the original zero extension of u over the real line. It is a physical Lebesgue moment, not a normalized probability-measure coefficient. On the original even sector, reflection equates moments at k and -k without conjugating u.

**Theorem 1.2 (Cosine coefficients of an originally even class).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_mode_inner_eq_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_mode_inner_eq_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a>0 and u belongs to originalEven(a). Pairing the two opposite Fourier characters gives the cosine, so the inner product with modeL2(a,n) is amplitude(a,n) times moment(a,u,n). The natural index n includes zero: the amplitude there is 1/sqrt(2*a), while for n>0 it is 1/sqrt(a). These nonzero amplitudes let vanishing cosine coefficients force vanishing moments.

**Theorem 1.3 (Interval Fourier coefficient normalization).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.fourierCoeffOn_eq_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.fourierCoeffOn_eq_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0, arbitrary u and every integer k, fourierCoeffOn on the interval from -a to a equals (2*a)^(-1) times the physical moment. The factor accounts for the entire interval length; physical dx is not silently replaced by normalized Haar measure.

**Definition 1.4 (Transport to normalized Haar L2).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With a>0, the Ioc lift gives an L2 class on AddCircle(2*a) for normalized Haar measure. Multiplication by sqrt(2*a) compensates for the dx/Haar mass ratio. The transport norm and coefficient theorems below record both scales of this concrete construction.

**Theorem 1.5 (Squared L2 norm as integral energy).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.l2_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.l2_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable space alpha, any measure mu and any complex L2 class u, the squared norm equals the integral of the pointwise squared norm with respect to mu. This identity applies both to the physical window and normalized Haar transport below, and to physical Lebesgue measure for the displaced signed modes.

**Theorem 1.6 (The transported squared norm is the physical squared norm).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every u and a>0, the unscaled lift has energy (2*a)^(-1) times the original energy. The square-root multiplier exactly restores the window L2 squared norm, using the original Ioc interval integral and the Haar integration identity.

**Theorem 1.7 (The transported Fourier coefficient has the required scale).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_fourierCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_fourierCoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and every integer k, the Fourier coefficient of circleTransport equals sqrt(2*a) times fourierCoeffOn of the original representative. Together with the interval coefficient identity, this is the physical moment divided by sqrt(2*a). Equality of representatives is used almost everywhere on the circle.

**Theorem 1.8 (Vanishing cosine coefficients determine the original even class).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_eq_zero_of_mode_inner_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_eq_zero_of_mode_inner_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a>0, u is originally AE-even, and its inner product with every natural cosine mode is zero. The nonzero amplitudes kill all nonnegative Fourier moments, and evenness supplies the negative indices. The proof then applies Mathlib's interval Parseval theorem tsum_sq_fourierCoeffOn directly to the original MemLp representative. All Fourier coefficients zero imply zero physical energy and hence u=0. Completeness is obtained from Parseval, rather than included in the definition of evenness or assumed as a basis hypothesis.

**Theorem 1.9 (The full original even sector is the closed complex cosine span).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.originalEven_eq_cosineClosure`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.originalEven_eq_cosineClosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0, originalEven(a) equals the topological closure of the complex linear span of all modeL2(a,n). Each mode already lies in the closed original even sector. Conversely, subtracting the orthogonal projection onto cosineClosure from an originally even u leaves an originally even vector orthogonal to every mode; the preceding injectivity theorem makes that residual zero. No finite upper mode cutoff or real-coefficient restriction occurs.

The argument uses standard Fourier characters, interval Parseval and Hilbert-space projection from Mathlib with explicit measure normalization. It supplies an analytic Hilbert/Fourier identification, with no literature novelty, canonical full Weil arithmetic/operator identification, signed positivity or Riemann-hypothesis conclusion claimed.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_fourierCoeff`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.circleTransport_norm_sq`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_eq_zero_of_mode_inner_eq_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.even_mode_inner_eq_moment`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.fourierCoeffOn_eq_moment`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.l2_energy`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.moment`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalEvenCosineComplete.originalEven_eq_cosineClosure`
- Dependency: [D5/S3/Weil/ZetaBridge/OriginalWindowEven](OriginalWindowEven.md)
