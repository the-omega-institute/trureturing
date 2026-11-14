# Exact Boolean rotation error fibers

## Abstract

Exact Boolean rotation error fibers

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

For every p and q and every positive epsilon, the Lebesgue volume of this closed sign chamber is epsilon to the power p plus q divided by p factorial times q factorial. The formula includes p or q equal to zero. Split the coordinates into two standard nonnegative simplices, each with total mass at most one. Multiplication by epsilon on the first summand and by minus epsilon on the second maps their product exactly onto the chamber. The absolute determinant is epsilon to the power p plus q. The two simplex volumes are supplied by ConditionalSubentropyGuessingBound.simplex_volume.

Distinct closed chambers can overlap only where at least one coordinate is zero. Such coordinate hyperplanes have Lebesgue measure zero.

**Theorem 1.8 (Exact volume of the signed body).**

Lean statement: `D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and positive epsilon, the Lebesgue volume of the signed body on Fin n is binomial(2n,n) times epsilon to the power n divided by n factorial. This includes dimension zero. Partition by the subset of nonnegative coordinates. The closed chambers cover the body and are pairwise disjoint outside coordinate hyperplanes. A coordinate permutation preserves volume and identifies each chamber with the signed orthant having p positive and n minus p negative coordinates. There are binomial(n,p) such choices. The sum of their reciprocal factorial coefficients equals binomial(2n,n) divided by n factorial, by the sum of squared binomial coefficients.

The volume identity is a Euclidean statement. The capacity lower bound uses it together with the exact error fiber and finite covering inequality on the product circle. The simultaneous grid construction for the upper bound is a separate obligation.

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

The theorem constrains finite codebooks with this prescribed subset-sum error relation. The grid upper bound and literal equality with the fixed planar rotation matrix decoder require separate constructions. It makes no claim about arbitrary decoders, computational time, finite hardware, learning or empirical physics.

## References

- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.Adequate`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.booleanError`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.circularError`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.exact_error_fiber`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.finite_codebook_lower_bound`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.nonnegative_sum_no_wrap`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signedBody`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signedOrthant`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume`
- Truth anchor: `D5/S3/Geometry/BooleanRotationCodebook.signed_orthant_volume`
- Dependency: [D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound](../Quantum/Measurement/ConditionalSubentropyGuessingBound.md)
