# Uniform Boolean rotation codebooks

## Abstract

Uniform finite-codebook storage bounds for the chapter35 Boolean planar-rotation family under one fixed Row-0 decoder

Exact application interface. For every integer n at least one and every real epsilon with 0 < epsilon < 2 pi / 3, set d(t) to the infimum over k in the integers of |t - 2 pi k| and Q_n to {0,1}^n. A finite C of real n-vectors is adequate when every theta has one chosen phi in C such that every x in Q_n satisfies d(sum_i x_i (theta_i - phi_i)) <= epsilon. The equivalent support encoding is the finite subset s = {i | x_i = 1}; its subset sum is the same sum because x is Boolean. The lower-bound theorem supplies |C| binomial(2n,n) epsilon^n at least n! (2 pi)^n. The product-grid theorem supplies one fixed C with |C| at most ceil(pi n / epsilon)^n. In both clauses the existential phi is outside the query quantifier, so the same phi serves every query for that theta, and C is fixed across all theta. The decoder is the literal real matrix R(alpha) = [[cos alpha, -sin alpha], [sin alpha, cos alpha]] applied to the stored subset sum; equality is literal matrix equality with period 2 pi and no global-phase quotient. No running-time, finite-hardware implementation, learning, self-update convergence, arbitrary-decoder lower-bound or empirical claim is asserted.

The signed-body volume formula and its orthant-product proof have established precedents. Kovačević and Tan, Lemma 2 and equation (17), give the constrained multiset-body volume and the same orthant decomposition; Colesanti's introduction, equation (5), records the Rogers–Shephard difference-body bound. The volume identity below formalizes this established simplex-difference calculation; the circle-covering application also uses the exact circular error fiber. Neither source is cited as proving the full no-wrap, prescribed-decoder or codebook result.

**Definition 1.1 (Circular error with a prescribed period).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.circularError`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.circularError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real L and t, circularError L t is the norm of the class of t in AddCircle L. For positive L this is the infimum of the absolute values of t minus kL over all integers k. The period is retained as L; for planar rotation matrices the prescribed period is 2 pi. This scalar error does not identify matrices up to global phase.

**Theorem 1.2 (Finite first crossing).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.nonnegative_sum_no_wrap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BooleanRotationCodebook.nonnegative_sum_no_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be any finite set of indices and a a real family. Suppose epsilon is nonnegative, three times epsilon is strictly less than L, and every a indexed by s lies between zero and epsilon. If the circular error of every subset sum is at most epsilon, the entire sum is at most epsilon. Induction removes one coordinate. The smaller sum is at most epsilon, so reinserting the coordinate gives a value between zero and twice epsilon. A nonzero multiple of L cannot be within epsilon of that interval. Thus its nearest multiple is zero and the entire sum remains at most epsilon.

**Definition 1.3 (One residual vector for every Boolean query).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.booleanError`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.booleanError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For one fixed residual vector a on a finite index type, booleanError L epsilon a requires circularError L of the sum over s to be at most epsilon for every finite subset s. Subsets are exactly the Boolean queries. The vector is chosen before quantifying over queries.

**Definition 1.4 (The signed simplex difference).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.signedBody`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.signedBody` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed body consists of vectors for which the sum of the positive parts and the sum of the negative parts are each at most epsilon. For positive epsilon this is epsilon times the difference of two standard coordinate simplices: split a into its positive and negative parts, and conversely bound those parts by the two nonnegative summands.

**Theorem 1.5 (Exact principal error fiber).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.exact_error_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BooleanRotationCodebook.exact_error_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type, nonnegative epsilon and L greater than three times epsilon, let a have all coordinates of absolute value at most L divided by two. Then all Boolean subset sums have circular error at most epsilon if and only if a belongs to the signed body. Singleton queries first bound each coordinate by epsilon. Apply the finite first crossing theorem to the nonnegative coordinates and then to the negated nonpositive coordinates. Conversely every subset sum lies between minus the total negative mass and the total positive mass; projection to the circle cannot increase its absolute value.

For L equal to 2 pi, the strict range is epsilon less than 2 pi divided by three. The fiber characterization covers every finite dimension, including zero. It concerns a fixed residual vector and supplies no arbitrary-decoder, computational-time, finite-hardware, learning or empirical conclusion. The capacity lower bound combines this characterization with the exact body volume and a covering argument. The grid upper bound is a separate construction.

**Definition 1.6 (A closed sign chamber).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.signedOrthant`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.signedOrthant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural numbers p and q, coordinates are indexed by the disjoint sum of Fin p and Fin q. The signed orthant is the signed body restricted to nonnegative coordinates on the first summand and nonpositive coordinates on the second. Zero coordinates belong to both adjacent closed sign chambers.

**Theorem 1.7 (Exact volume of a sign chamber).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.signed_orthant_volume`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BooleanRotationCodebook.signed_orthant_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p and q and every positive epsilon, the Lebesgue volume of this closed sign chamber is epsilon^(p+q) / (p! q!), with both factorials in the denominator. The formula includes p or q equal to zero. Split the coordinates into two standard nonnegative simplices, each with total mass at most one. Multiplication by epsilon on the first summand and by minus epsilon on the second maps their product exactly onto the chamber. The absolute determinant is epsilon^(p+q). The two simplex volumes are supplied by ConditionalSubentropyGuessingBound.simplex_volume.

Distinct closed chambers can overlap only where at least one coordinate is zero. Such coordinate hyperplanes have Lebesgue measure zero.

**Theorem 1.8 (Exact volume of the signed body).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Kovačević; D. Tan (2018). *Codes in the Space of Multisets—Coding for Permutation Channels with Impairments*. URL: <https://arxiv.org/html/1612.08837v5>.

*Commentary.*

For every natural n and positive epsilon, the Lebesgue volume of the signed body on Fin n is binomial(2n,n) times epsilon to the power n divided by n factorial. This includes dimension zero. Partition by the subset of nonnegative coordinates. The closed chambers cover the body and are pairwise disjoint outside coordinate hyperplanes. A coordinate permutation preserves volume and identifies each chamber with the signed orthant having p positive and n minus p negative coordinates. There are binomial(n,p) such choices. The sum of their reciprocal factorial coefficients equals binomial(2n,n) divided by n factorial, by the sum of squared binomial coefficients.

The volume identity is a Euclidean statement. Kovačević and Tan's Lemma 2 gives the same volume formula and orthant-product argument for integer radius and positive dimension. Positive real radii follow by dilation of the same body. Equivalently, in dimensions at least two the formula is the simplex equality case of the classical Rogers–Shephard difference-body inequality, as stated in Colesanti's introduction, equation (5). Neither the formula nor this orthant calculation is claimed as new. The capacity lower bound uses the identity together with the exact error fiber and finite covering inequality on the product circle. These Euclidean volume precedents do not by themselves give the circular error fiber or the codebook bounds.

**Definition 1.9 (A finite codebook with uniform queries).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.Adequate`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.Adequate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural dimension n, period L and error epsilon, Adequate n L epsilon C means that for every real parameter vector theta there exists one phi in the finite codebook C such that every Boolean subset query has circular error at most epsilon for theta minus phi. The chosen codeword works simultaneously for all queries, and C is fixed before theta.

**Theorem 1.10 (Uniform finite-codebook capacity lower bound).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.finite_codebook_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BooleanRotationCodebook.finite_codebook_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, positive epsilon, period L greater than three times epsilon, and adequate finite codebook C, its cardinality times binomial(2n,n) times epsilon to the power n is at least n factorial times L to the power n. In particular L equal to 2 pi gives the stated planar-rotation capacity lower bound throughout zero less than epsilon less than 2 pi divided by three.

Equip each additive circle of period L with Haar measure of mass L. The product circle has mass L to the power n. Lift its zero-codeword error fiber to the centered period box using the measure-preserving coordinate quotient maps. Within this box the exact error fiber theorem identifies the lifted fiber with a subset of the signed body, whose volume is binomial(2n,n) times epsilon to the power n divided by n factorial. Adequacy covers the product circle by one translate of this fiber per codeword. Translation invariance and finite subadditivity give the cardinality inequality.

The theorem constrains finite codebooks with this prescribed subset-sum error relation. The product grid upper bound supplies a fixed decoder with literal planar rotation matrices. It makes no claim about arbitrary decoders, computational time, finite hardware, learning or empirical physics. The classical Rogers–Shephard inequality quoted by Colesanti is a related volume precedent, not the proof of this torus-covering statement.

**Definition 1.11 (Literal planar rotation).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.rotation`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.rotation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real two by two matrix has first row cos alpha and minus sin alpha, and second row sin alpha and cos alpha. Equality is literal matrix equality.

**Definition 1.12 (Prescribed subset query decoder).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.row0Decoder`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.row0Decoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For one stored real vector phi and a Boolean subset s, the fixed decoder returns the literal rotation through the sum of phi coordinates indexed by s.

**Definition 1.13 (One codeword for all literal matrix queries).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.FixedDecoderAdequate`

*Formalization.* `D5/S3/Geometry/BooleanRotationCodebook.FixedDecoderAdequate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rotation function is periodic with period 2 pi. Every parameter vector selects one codeword from the fixed codebook before the query. Every subset query admits a real angular residual of absolute value at most epsilon giving exact equality between the target rotation and the rotation at the stored subset sum plus that residual.

**Theorem 1.14 (Uniform product grid upper bound).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.finite_codebook_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BooleanRotationCodebook.finite_codebook_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive dimension n, positive period L and positive epsilon, there exists an adequate finite codebook of cardinality at most ceil(L n / (2 epsilon)) to the power n. Put m equal to that ceiling and use the Cartesian product of m equally spaced points on each circle. Round m theta divided by L to a nearest integer and reduce its circular class to one of the m grid points. The coordinate error is at most L divided by 2m. One vector of these choices is selected before any query. Every subset sum has circular error at most the sum of its coordinate errors, hence at most nL divided by 2m, which is at most epsilon. The grid is fixed for all parameter vectors. At L equal to 2 pi, the same codeword simultaneously realizes every query using the prescribed literal real matrix decoder. The scalar error bound is equivalent to existence of a real angular residual delta of absolute value at most epsilon for which R(alpha) equals R(beta plus delta). Equality of the cosine and sine entries is equivalent to equality modulo 2 pi; it does not identify matrices up to global phase. The matrix-valued function has literal period 2 pi.

## References

- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.Adequate`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.FixedDecoderAdequate`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.booleanError`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.circularError`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.exact_error_fiber`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.finite_codebook_lower_bound`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.finite_codebook_upper_bound`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.nonnegative_sum_no_wrap`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.rotation`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.row0Decoder`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signedBody`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signedOrthant`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signed_orthant_volume`
- Dependency: [D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound](../Quantum/Measurement/ConditionalSubentropyGuessingBound.md)
