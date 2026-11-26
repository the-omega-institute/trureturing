---
bibkey: hagele2026refinedbmv
authors: Daniel Hägele
year: 2026
title: "On the lower bound of the refined Bessis–Moussa–Villani conjecture: proof of the cases S6,3 and S7,3 for 3 × 3 matrices"
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
claim: Section 7 identifies the dimension-three refined BMV lower bound for (5,3) and the bounds for (3,3) and (4,3) in dimensions at least four.
strata_touched:
  - D5/S3/Quantum/Analysis/RefinedBMV84
  - D5/S3/Quantum/Analysis/RefinedBMV/NineFour
  - D5/S3/Quantum/Analysis/RefinedBMV/TenFour
  - D5/S3/Quantum/Analysis/RefinedBMV/ThirteenFour
  - D5/S3/Quantum/Analysis/RefinedBMV/SeventeenFour
  - D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/WordMean
  - D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumProduct
  - D5/S3/Quantum/Analysis/RefinedBMV/BinaryGramConditioning
  - D5/S3/Quantum/Analysis/RefinedBMV67
  - D5/S3/Quantum/Analysis/RefinedBMV54
  - D5/S3/Quantum/Analysis/RefinedBMV44
  - D5/S3/Quantum/Analysis/RefinedBMV33
  - D5/S3/Quantum/Analysis/RefinedBMV/Tracial/Bound
  - D5/S3/Quantum/Analysis/RefinedBMVLowerBound
  - D5/S3/Quantum/Analysis/RefinedBMV43
  - D5/S3/Quantum/Analysis/RefinedBMV/GroupedFourThree
  - D5/S3/Quantum/Analysis/RefinedBMV43Kernel
  - D5/S3/Quantum/Analysis/RefinedBMVDimThree
  - D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate
  - D5/S3/Quantum/Analysis/RefinedBMVDimThreePairing
  - D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues
  - D5/S3/Quantum/Analysis/RefinedBMV/DimFour
  - D5/S3/Quantum/Analysis/RefinedBMV/DimFourScalar
  - D5/S3/Quantum/Analysis/RefinedBMV/DimFourWalk
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometricIntervalSign
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripKernel
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripLowSign
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripWideSign
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapReplay
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourKernel
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirds
  - D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleSign
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

## The grouped trace comparison at bidegree (4,3)

For positive semidefinite complex matrices `C` and `R` of any common
finite size, the mean trace of the 35 words with four copies of `C`
and three of `R` is at least `Tr(R² C² R C²)`. After diagonalizing
`C`, a cyclic polynomial identity expresses the gap using a kernel
for each spectral value. Each kernel is a sum of a rank-one kernel
and a weighted Cauchy kernel. The Schur product theorem gives the
bound, including zero eigenvalues and arbitrary multiplicities.

Hägele's 2007 sum-of-squares certificate gives the same grouped word
with coefficient one fifth in the lower bound for the mean. See DOI
[10.1007/s10955-007-9327-8](https://doi.org/10.1007/s10955-007-9327-8)
and Klep and Schweighofer's reproduction in §3, equation (4),
[arXiv:0710.1074v4](https://arxiv.org/abs/0710.1074v4).
Heinävaara's commutation-measure moment, Lemma 2.5, equation (15),
gives a different linear combination of the five cyclic classes.
[arXiv:2602.10373v1](https://arxiv.org/abs/2602.10373v1)

Hägele's 2026 Theorem 2 and §7(iii) concern the fractional-product
comparator. Dinh, Le and Vuong's Theorem 4.2 concerns the pinched
comparator. Both comparators can be strictly smaller than the grouped
trace. A search of these sources and their citations found no prior
proof of the unrestricted coefficient-one comparison.
[arXiv:2610.31851v1](https://arxiv.org/abs/2610.31851v1)

## Four copies of each factor

Section 7(iii) identifies the three-dimensional (4,4) case. For every
finite complex PSD pair A and B, the repository proof bounds the mean of
the seventy word traces below by the trace of (AB)^4. The fourth moment
of the Hermitian part of AB and the cyclic word counts combine to express
the trace gap as a sum of nonnegative terms. Ando, Hiai and Okubo's
Corollary 2.2(ii) gives the two weighted word comparisons used in the
sum. Their Corollary 2.4 gives the upper word bound.
The dyadic comparison from Hägele's Lemma 2 gives the exponential result.

## Five copies of the first factor

For the (5,4) comparison, the mean of the 126 word traces dominates
the trace of A(AB)^4 by a sum of four Frobenius squares weighted by A.
Three further Frobenius squares compare this intermediate trace to
the trace of (A^(5/4) B)^4. The product proof permits a singular PSD
first factor and an arbitrary Hermitian second factor. The dyadic
comparison in Hägele's Lemma 2 gives the exponential lower bound.
Burgdorf's Theorem 1.5 and Example 2.1(b) in arXiv:0802.1153v2
give cyclic square decompositions for the classical coefficient bound.

## Six and seven copies of the first factor

The lower comparisons at (6,4) and (7,4) hold in every finite complex
dimension. The mean of the 210 words at (6,4) dominates the trace of
`(A^(3/2) B)^4` for PSD A and B. The mean of the 330 words at (7,4)
dominates the trace of `(A^(7/4) B)^4` for PSD A and Hermitian B.
Both results include singular A. The cyclic coefficient identities
compare the means with balanced integer words. Three rational Gram
blocks give the six-copy comparison, including one weighted by B on
both sides. The seven-copy comparison uses a Gram block weighted by A.
The dyadic comparison gives the exponential bounds with exponents
`6H + 4K` and `7H + 4K`.

## Eight copies of the first factor

The (8,4) product comparison holds for every finite complex PSD pair.
The mean of the 495 word traces dominates the fourth trace of the
Hermitian part of A^(3/2) B A^(1/2) by three rational Gram blocks.
The fourth trace of that Hermitian part bounds the trace of (A^2 B)^4.
The proof treats singular A and B directly. The dyadic trace-power
comparison from Lemma 2 gives the corresponding exponential bound.

## Nine copies of the first factor

At (9,4), the mean of the 715 word traces dominates the trace of
(A^(9/4) B)^4 for PSD A and Hermitian B in every finite complex
dimension, including singular A. One rational positive semidefinite
Gram matrix on 15 half-words, weighted by A, compares the mean with
the word trace with cyclic gaps (3,2,2,2). Two trace Cauchy–Schwarz
inequalities give the balanced bound. The dyadic comparison from
Hägele's Lemma 2 gives the lower bound by the trace of exp(9H + 4K)
for the same word mean on exp H and exp K.

The bounded search found no earlier proof of the unrestricted (9,4)
lower bound. It located lower bounds for small p or restricted dimension
(arXiv:2611.00129), results on upper-bound failure (arXiv:2603.19927 and
arXiv:2605.17782), and work on the Stieltjes transform (arXiv:2611.03208).

## Ten copies of the first factor

At (10,4), the mean of the 1001 word traces dominates the trace of
(A^(5/2) B)^4 for PSD A and B in every finite complex dimension,
including singular A and B. Three rational positive semidefinite Gram
blocks, of sizes 21, 15 and 6 with weights I/I, A/A and B/B, compare
the mean with the trace of (A^3 B A^2 B)^2, with cyclic gaps (3,2,3,2).
Trace Cauchy–Schwarz gives the fractional-power bound. Hägele's Lemma 2
gives the lower bound by the trace of exp(10H + 4K) for the same word
mean on exp H and exp K with Hermitian H and K.

Independent rational review checked all 73 cyclic coefficients and the
three Gram factorizations. Historical priority remains unverified after
bounded searches covering arXiv:2611.00129, 0802.1153, 2611.03208,
2610.31851 and 2611.23122.

## Thirteen copies of the first factor

At (13,4), the mean of the real parts of the 2,380 ordered word traces
dominates the real part of the trace of `(A^(13/4) B)^4` for PSD A and
Hermitian B in every finite complex dimension, including singular A.
Hägele formulates the product comparison for positive semidefinite
factors in Section 1. The proof uses an A-weighted
rational Gram matrix on 28 half-words with 18 positive factorization
weights. The cyclic coefficient identity compares the mean with the
trace of the word with gaps (4,3,3,3). Two trace Cauchy–Schwarz
inequalities give the fractional-power bound. The dyadic comparison
from Lemma 2 gives the lower bound by the real part of the trace of
`exp(13H + 4K)` for the same word mean on `exp H` and `exp K`.

## Seventeen copies of the first factor

At (17,4), for positive semidefinite A and Hermitian B in every finite
complex dimension, the mean of the real parts of the 5,985 ordered
word traces dominates the real part of the trace of `(A^(17/4) B)^4`.
The argument includes singular A. A rational Gram factorization on
45 half-words with 28 positive weights compares the word mean with
the trace of the cyclic word with gaps (5,4,4,4). The proof reuses the
four-gap identity to check the cyclic coefficients. Two trace
Cauchy–Schwarz inequalities give the fractional-power comparison.
The dyadic argument in Hägele's Lemma 2 gives the corresponding
lower bound by the trace of `exp(17H + 4K)`.

The literature check found lower bounds with different hypotheses or
comparators. Hägele's Theorem 1.2 treats smaller degrees and dimensions.
Burgdorf's Theorem 1.5 proves four-copy coefficient positivity.
Dinh, Le, and Vuong's Theorem 4.2 uses a spectrally pinched comparator.

## Four copies of the second factor near the identity

For every natural number `p` and every finite complex dimension, take
Hermitian `H`, positive semidefinite `B`, and `A = exp H`. If
`p ‖H‖op ≤ 1/100000`, the mean of `Re Tr(w)` over all ordered words `w`
with `p` copies of `A` and four copies of `B`, minus
`Re Tr((A^(p/4) B)^4)`, is at least `p² ‖B(HB − BH)‖F² / 25`.
Here `Tr` is the unnormalized matrix trace, `A^(p/4)` is the real spectral
power, and `‖·‖op` and `‖·‖F` denote the operator and Frobenius norms.
For `p > 0` the sufficient radius for `‖H‖op` is `1/(100000 p)`, independent
of the dimension. At `p = 0` the smallness condition is automatic and
the lower bound for the gap is zero.

The repository theorem `wordMean_sub_balanced_ge` proves this sufficient
neighborhood of the identity for the four-copy product lower comparison
in [Hägele, arXiv:2611.00129](https://arxiv.org/abs/2611.00129v1).

## Four copies of the second factor on singular three-value spectra

For every positive integer `p`, let `A, B` be positive semidefinite
matrices of any common finite complex size. Suppose the spectrum of
`A` is contained in `{0, r, t}` for `0 < r < t`. Then the mean trace
over the ordered words with `p` copies of `A` and four copies of `B`
is at least `Tr((A^(p/4) B)^4)`. The spectral multiplicities and `B`
are unrestricted.

The cyclic four-gap expansion groups the difference into contractions
with three positive semidefinite Gram matrices and nonnegative
alternating traces. The Gram entries use finite geometric sums and
balanced spectral powers. Five scalar polynomial inequalities give the
Schur conditions. After substituting the middle-to-top spectral ratio
and its `p/8) power as exponentials, each polynomial is a finite
exponential sum. Exact integer checks certify all coefficients of the
required initial-value polynomials in `p - 1`. The differential
equations of the exponential factors propagate those signs for every
nonnegative log gap.

The argument addresses a spectral class of Hägele's four-copy
product lower comparison. The related arXiv results 0802.1153,
2611.12498 and 2610.31851 concern ordinary coefficient positivity,
positive measures for fixed occurrences and a pinched comparison,
respectively. Historical priority for the spectral result has not
been established.

## Sharp conditioning for four-copy Gram blocks

For each positive integer p and each pair of distinct positive spectral
values, let f and f' be the four-slot deficits with multiplicities
three and one in the two orders. Let g be the deficit with multiplicities
two and two. The spectral Gram block has diagonal f, f' and entry g/2
off the diagonal. The repository proves that g² is strictly less than
2ff' and that every smaller uniform constant fails for some p and pair
of strictly positive values. The proof clears the geometric-sum
denominators and checks the coefficient signs of the resulting
exponential polynomial after subtracting a strictly positive term.

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
controlled radical term preserve the strict sign. On the central interval
from one half to four, the same mixed sign holds from gap four. A sharper
bound couples the linear correction to the leading square, and a
divided-difference average bounds the radical contribution. When the gap
is greater than eleven, the sign holds for all positive lower coordinates.

For first degrees at least eleven, the original logarithmic kernel also
has strictly negative mixed derivative when the lower coordinate is in
(0, 1/2] and the log gap is in (0, 1]. Factoring the marginal zeros gives
a continued integrand. For upper coordinates up to one, the low-strip
enclosure gives its strict sign. From one to three halves, exact interval
bounds on the marginal Taylor polynomials and the tilted joint moments
give strict positivity at every integration point in the derivative identity.

On the same range of lower coordinates, the mixed derivative is also
strictly negative for gaps in [1, 3/2]. Three closed scalar bands cover
the interval [1, 2], which contains every shifted gap in the geometric
endpoint comparison.

For first degrees at least eleven, the repository also proves strict
negativity of the mixed derivative for every ordered pair of logarithmic
coordinates with lower coordinate at least four. Short gaps through two
and gaps from four have separate bounds. Between two and four, a finite
cover and dyadic Taylor enclosures preserve the sign in the original
normalized kernel.

For first degrees at least eleven and lower coordinate in \((0,1/2]\),
the logarithmic kernel has strictly negative mixed derivative at all
gaps at least one. Geometric reduction controls the scaled scalar
through integration gap seven halves with exact Taylor enclosures. The
analytic tail estimate supplies the sign past that threshold.

For first degrees at least eleven, the short-gap result extends to lower
coordinate at least ten thirds and all positive gaps through two. The
proof combines the certified curvature and slope of the short-gap profile
with a bound for the radical derivative. The fourth moment strengthens
the marginal slope estimate for gaps at least one.

For every degree at least eleven, the mixed derivative is strictly
negative throughout the closed middle band with lower coordinate from
one half to four and gap from one to four. The proof covers the band
with 39 cells and verifies the original derivative on each cell using
exact Taylor bounds and uniform estimates in the degree.

## Quantitative degree-three gap for finite traces

In a unital C*-algebra with a positive finite trace, let the gap be the
mean trace of the twenty words with three copies of each positive factor
minus the trace of the cube of their product. The repository theorem
`wordMean_three_trace_gap` bounds three times the square of the trace
of the commutator's adjoint times the commutator by forty times the trace
of the product times the gap. A rank-one term of the centered cubic
kernel survives approximation by positive functions of the first factor.
Under a faithful trace, the bound forces the factors to commute at equality.

- [Hägele, arXiv:2611.00129v1](https://arxiv.org/abs/2611.00129v1).
- [Cha–Lee, the separate upper-bound counterexamples](https://arxiv.org/abs/2603.19927).
