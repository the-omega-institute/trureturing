---
bibkey: hagele2026refinedbmv
authors: Daniel Hägele
year: 2026
title: "On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices"
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
claim: Section 7 identifies the dimension-three refined BMV lower bound for (5,3) and the bounds for (3,3) and (4,3) in dimensions at least four.
strata_touched:
  - D5/S3/Quantum/Analysis/RefinedBMV33
  - D5/S3/Quantum/Analysis/RefinedBMVLowerBound
  - D5/S3/Quantum/Analysis/RefinedBMV43
  - D5/S3/Quantum/Analysis/RefinedBMV43Kernel
  - D5/S3/Quantum/Analysis/RefinedBMVDimThree
  - D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate
  - D5/S3/Quantum/Analysis/RefinedBMVDimThreePairing
  - D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues
  - D5/S3/Quantum/Analysis/RefinedBMV/DimFour
  - D5/S3/Quantum/Analysis/RefinedBMV/DimFourScalar
  - D5/S3/Quantum/Analysis/RefinedBMV/DimFourWalk
  - D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic
  - D5/S3/Quantum/Analysis/RefinedBMVUniformCorner
  - D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumReduction
  - D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate
license: citation-only
triage: anchor
---

# The refined BMV lower bound with three occurrences of one factor

## Verified locator

DOI: 10.48550/arXiv.2611.00129

Source: https://arxiv.org/abs/2611.00129v1

Theorem 1 and Lemma 2 give the known low-dimensional cases and the reduction
from a stronger trace-power comparison. Section 7(iii), page 8, identifies
the higher-dimensional cases with word counts `(3,3)` and `(4,3)`. Sections 3–5 derive the
closed-walk trace expansion and the three-dimensional comparison.

## Scope and conventions

For complex Hermitian matrices `H, K`, take the average of the traces of the
twenty words with three letters `exp H` and three letters `exp K`. The lower
bound is `Tr exp(3H + 3K)`. The mean is real by reversal of the
words and conjugation of their traces.

The four-dimensional proof first shows that the mean for positive
semidefinite `A, B` is at least `Tr((AB)^3)`. Shifting one
matrix by its smallest eigenvalue gives a zero eigenvalue. A symmetric
rational decomposition of the cubic trace defect then groups all walks
at each center into a single quadratic form. The four coefficient
matrices are positive semidefinite by Cauchy and Schur complement
identities. The Schur product theorem preserves each grouped inequality
with complex entries. The dyadic trace-power comparison and Lie–Trotter
give the exponential bound.

The general `(3,3)` proof uses a different symmetric coefficient in the
same cubic trace identity. At each positive spectral center its matrix is
a rank-one positive semidefinite term plus a diagonal congruence of the
Cauchy matrix on the positive eigenvalues. The zero center has only the
Cauchy term. This decomposition gives the product bound in every finite
dimension, and the same trace-power comparison gives the exponential bound.
The symmetric coefficient was found in an independent GPT Pro review, then
checked by exact algebra and used in the formal proof.

The `(4,3)` proof uses the eigenvalues of the positive semidefinite cube
root of the first factor. The centered coefficient matrices are sums of
a Gram matrix from four polynomial features and a weighted Cauchy matrix.
This coefficient identity treats every finite dimension and gives the
trace-power comparison. Apply it to `exp(H/3)` and `exp K` and use the same
dyadic argument to obtain the lower bound `Tr exp(4H + 3K)`.

Section 7(ii–iii) identifies the case `(5,3)` in dimension three and
describes the scalar certificate route for three copies of the second
factor. For `p = 5, 6, 7`, the dimension-three proof uses Proposition 2
and the pairing of Lemma 5. The certificate compares the square of the
mixed deficit with the square of a sum of two square roots. Substituting
ordered cube roots as a nonnegative base and two nonnegative increments
reduces this comparison to the signs of exact integer coefficients.
The kernel checks the signs by a packed integer comparison, using
homogeneity and a bound on the coefficient sizes. The pairing uses the
unique index triangle in dimension three. The all-dimensional proofs
use centered coefficient matrices.

For five, six, or seven first factors, the same scalar certificate applies
in every finite dimension if the first factor has at most three distinct
eigenvalues. If `P_i` is the projection of a spectral label and `B` is the
second PSD factor, the paired terms are cubic traces of
`C_i = sqrt(B) P_i sqrt(B)`. The Hilbert–Schmidt pairing of
`C_i sqrt(C_k)` and `C_j sqrt(C_k)` supplies the bound at the center
`k`, including when some projections have rank zero. The exponential
comparison uses the exact dyadic limit from Lemma 2.

For matrices of size four, the accompanying proof
`p-three-dimension-four-proof.txt` derives a comparison using all four
oriented triples. An ordered-cube-root coefficient inequality bounds each
squared geometric mean by the squared mixed defect. The phase choice in
each column gives a nonnegative trace of a positive quadratic form with
the same repeated-index contribution as the cubic walk. With three
negative faces, the two negative edges in a column form a path and the
cycle product determines the real-part sign on its third edge. The
formal comparison uses this proof for `p = 5, 6, 7` together with Hägele's
word expansion and dyadic trace-power comparison.

The repository proof answers the unrestricted `(5,3)` question from
Hägele's Section 7 in every finite dimension, with any number of distinct
eigenvalues of the first factor. For complex positive semidefinite `A, B`,
the mean trace of the 56 words with five copies of `A` and three copies
of `B` is at least `Tr((A^(5/3) B)^3)`, with `A^(5/3)` defined by spectral
calculus. Exact polynomial signs give nonnegative rectangle differences
of the normalized upper kernel on each sorted finite sample. These
differences telescope to a weighted Gram sum of interval indicators.
Diagonal rescaling and a rank-one lower block give the centered kernels,
whose Schur products with `B` in the eigenbasis give nonnegative cubic
walk contributions. For complex Hermitian `H, K` in every finite dimension,
Hägele's dyadic trace comparison in Lemma 2 gives the lower bound
`Tr exp(5H + 3K)` for the same word mean on `exp H, exp K`.

For every number of first factors, the scalar mixed defect
dominates the geometric mean of the two repeated-root defects at the
largest spectral center. Compress the triangular coefficient matrix of
the complete homogeneous polynomial to the two root vectors. The signs
of its two-by-two minors give reverse Cauchy–Schwarz after compression.
Ordinary Cauchy–Schwarz on the two repeated-root defects and their
geometric corrections transfers the inequality to the defect. This
proves the corner inequality used in the interval proof. Equality
occurs exactly when the first two roots coincide or the degree is zero.

The uniform three-spectrum reduction uses the cyclic three-gap expansion
of Proposition 2 and the trace pairing from Lemma 5. The complete
homogeneous sum is a second divided difference of a monomial. Its
explicit formulas at distinct and repeated nodes clear the denominators
in a quartic scalar discriminant. Two log gaps then describe the strict
positive-root case. Continuity extends a nonnegative discriminant to
ties and zero roots. For each first degree, positivity of this scalar
polynomial implies the product and exponential bounds in arbitrary
finite dimension when the first matrix has at most three spectral values.

The coefficient certificate proves the required positivity for every positive
integer degree. Its 12,476 terms are checked against the factored discriminant
by an injective mixed-radix integer evaluation. The resulting exponential sum
has 65 affine rates along each log gap. For each pair of prefixes of these rates,
the associated mixed derivative at the origin is a polynomial in `p - 1`.
A packed integer sign check certifies its nonnegative coefficients. The
first-order differential equations for the exponential factors propagate
the signs along both log gaps. The trace reduction therefore gives the
product and exponential bounds throughout the three-spectrum class, including
arbitrary spectral multiplicities and singular positive semidefinite inputs.

The same interval Gram proof treats the unrestricted `(6,3)` and
`(7,3)` comparisons. The product bounds are
`84 Tr((A^2 B)^3) <= Tr S_{9,3}(A,B)` and
`120 Tr((A^(7/3) B)^3) <= Tr S_{10,3}(A,B)`.
The corresponding exponential bounds hold for all finite Hermitian
`H, K` with exponents `6H + 3K` and `7H + 3K`, respectively.
Lean checks the ordered mixed derivative and boundary polynomials at
each degree by exact integer arithmetic. The all-degree trace-word
identity and centered Schur argument transfer these scalar signs to
the matrix bounds without a restriction on spectral multiplicities.
The literature search found no matching unrestricted proof for either
degree. Dinh, Le, and Vuong's arXiv:2610.31851v1, Theorem 4.2,
establishes the lower comparison with the spectrally pinched factor.

The interval certificate also proves the unrestricted product and
exponential comparisons at first degrees eight, nine, and ten, with
three copies of the second factor. In Hägele's total-word notation,
the product lower bounds for `Tr S_{11,3}`, `Tr S_{12,3}`, and
`Tr S_{13,3}` are the trace of the cube of `A^(p/3) B` multiplied
by 165, 220, and 286, respectively. The result permits any finite
dimension and includes singular positive semidefinite factors. The
exponential bounds have exponents `8H + 3K`, `9H + 3K`, and
`10H + 3K`. Literature searches located no matching unrestricted
proof of these cases in the sources examined.

The repository proof treats the product comparison from Hägele's Section
7(ii–iii) for every positive integer `p` in every finite dimension when
the complex positive semidefinite first factor `A` is singular and has at
most four distinct eigenvalues. The second factor `B` is any complex
positive semidefinite matrix of the same size. The mean trace of the words
with `p` copies of `A` and three of `B` is at least `Tr((A^(p/3) B)^3)`,
with `A^(p/3)` defined by spectral calculus. At zero, curvature bounds for
the normalized scalar profile give a finite interval Gram sum. At each
positive center, the ordered quartic and the corner inequality control
the block of at most two distinct larger eigenvalues. The cyclic trace
identity and Schur product give the product comparison.

For arbitrary spectral multiplicities, the repository reduces the
upper-block positivity condition at each positive first degree to one
scalar sign. The mixed derivative of the normalized logarithmic kernel
must be nonpositive at every pair (0<u<v). The two endpoint limits
complete the rectangle inequalities on finite ordered samples. At a
zero center, the unnormalized matrices converge on each fixed sample,
and the positive semidefinite cone is closed. The trace inequalities
then follow at every degree for which the scalar sign is established.

For first degrees at least eleven, the mixed derivative is strictly negative
when the lower logarithmic coordinate lies in (0, 4] and the gap is at least
six. The leading square controls the potentially adverse linear term before
upper normalization. The positive decreasing upper factor and the separately
controlled radical term preserve the strict sign. When the gap is greater
than eleven, the sign holds for all positive lower coordinates.

- [Hägele, arXiv:2611.00129v1](https://arxiv.org/abs/2611.00129v1).
- [Cha–Lee, the separate upper-bound counterexamples](https://arxiv.org/abs/2603.19927).
