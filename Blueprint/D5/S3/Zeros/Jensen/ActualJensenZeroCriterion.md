# Cauchy zero exclusion for the actual Jensen tower

## Abstract

Local uniform approximation by the actual fixed-shift theta Jensen polynomials gives a zero-exclusion criterion.

**Definition 1.1 (Real roots of a complex polynomial).**

Lean statement: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.AllRootsReal`

*Formalization.* `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.AllRootsReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex polynomial p, AllRootsReal(p) says that every complex z with p(z)=0 has imaginary part zero.

**Theorem 1.2 (Cauchy zero exclusion under locally uniform limits).**

Lean statement: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.allZerosReal_of_locallyUniform`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.allZerosReal_of_locallyUniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let l be any nontrivial filter on any index type. Let p be a family of complex polynomials whose evaluations converge locally uniformly throughout the complex plane along l to an entire function F. Assume F(0) is nonzero and eventually along l each p has only real roots. Then every complex zero of F has imaginary part zero.

Around a putative nonreal zero of F, choose a disk within the complement of the real axis and small enough to isolate the zero. The boundary minimum of the norm of F is positive. A sufficiently close polynomial is zero-free throughout the disk and has norm at least half that minimum on the boundary. Cauchy's order-zero estimate for its reciprocal gives the same lower bound on the polynomial's norm at the center, contradicting convergence there.

**Theorem 1.3 (The theta source in the xi-square coordinate).**

Lean statement: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.sourceF_eq_xiSquareSource`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.sourceF_eq_xiSquareSource` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire theta cosine-square source F equals the normalized xi-square function as a function on the whole complex plane. The latter evaluates xi at one half plus i times a square root of z and divides by xi at one half. Apply the theta Fourier identity to both signs of the square root. Xi reflection identifies the two readings, and the cosine identity takes their average.

**Theorem 1.4 (Invariance of root reality under reflection).**

Lean statement: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.sourceJensen_real_iff_reflected`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.sourceJensen_real_iff_reflected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree d, the actual sourceJensenPolynomial(d) has only real roots if and only if sourcePolynomial(d) has only real roots. The second is the first composed with X mapped to minus X, which sends roots by z mapped to minus z.

**Theorem 1.5 (Riemann hypothesis from every positive degree).**

Lean statement: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.rh_of_actual_jensen_tower`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.rh_of_actual_jensen_tower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the actual fixed zero-shift sourceJensenPolynomial(d) has only real roots for every natural d at least one. Then the Riemann hypothesis holds.

The reflected polynomials converge locally uniformly to the theta cosine-square source by the fixed-window approximation estimate, and the source takes value one at zero. Cauchy zero exclusion puts all its zeros on the real axis. For a nontrivial zeta zero s, its square-source coordinate is the square of minus i times (s minus one half). Its imaginary part is twice Im(s) times (one half minus Re(s)). Zeta has no real zero in the open critical interval, so Re(s) equals one half.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.AllRootsReal`
- Truth anchor: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.allZerosReal_of_locallyUniform`
- Truth anchor: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.rh_of_actual_jensen_tower`
- Truth anchor: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.sourceF_eq_xiSquareSource`
- Truth anchor: `D5/S3/Zeros/Jensen/ActualJensenZeroCriterion.sourceJensen_real_iff_reflected`
- Dependency: [D5/S3/Zeros/ActualZeroGeometry](../ActualZeroGeometry.md)
- Dependency: [D5/S3/Zeros/Jensen/ActualSourceJensenFixedWindow](ActualSourceJensenFixedWindow.md)
- Dependency: [D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder](../Resolvent/XiSquareExteriorRemainder.md)
