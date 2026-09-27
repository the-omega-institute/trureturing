# Binary carry and phase-preserving quotient coverage

## Abstract

A periodic family of affine congruence rows descends through a binary quotient by retaining activation, direction and carry for the same original phases.

Fix a positive integer M and period N equal to twice M. A row has positive modulus e dividing N, integer coefficients a and b, and an arbitrary integer phase c. The rows may be indexed by any type, including an empty type. Thus the results apply to every finite family without requiring distinct moduli or distinct congruence classes.

**Definition 1.1 (The original affine congruence).**

Lean statement: `D5/S3/Arith/Covering/BinaryCarryQuotient.covers`

*Formalization.* `D5/S3/Arith/Covering/BinaryCarryQuotient.covers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row covers the integer pair (k,l) exactly when e divides a k plus b l minus c. Equivalently, a k plus b l is congruent to c modulo e. The phase belongs to the row and is shared by every occurrence of that row in the quotient predicates.

**Definition 1.2 (Scaling to the common period).**

Lean statement: `D5/S3/Arith/Covering/BinaryCarryQuotient.scaled`

*Formalization.* `D5/S3/Arith/Covering/BinaryCarryQuotient.scaled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write F for N/e times the original affine expression. Divisibility by e of the original expression is equivalent to divisibility of F by N. A top row is exactly a row for which N/e is odd. Its normal is the pair (a modulo 2, b modulo 2); its activity at a basepoint means divisibility of F by M. Every top normal is assumed nonzero. This is the only consequence of primitivity needed here.

**Definition 1.3 (Three ways to cover a binary fiber).**

Lean statement: `D5/S3/Arith/Covering/BinaryCarryQuotient.Criterion`

*Formalization.* `D5/S3/Arith/Covering/BinaryCarryQuotient.Criterion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first alternative is a lower row covering the basepoint. A lower row is precisely a row outside the top cohort.

The second is a pair of distinct top indices with equal normals. Both rows must be active, and their two scaled values must sum to M modulo N. These are complementary parallel lines.

The third is a triple of top rows whose normals are pairwise distinct. All three rows must be active, and their scaled values must sum to zero modulo N. The nonzero-normal hypothesis makes these exactly the three nonzero binary directions and also forces the three indices to be distinct.

**Theorem 1.4 (Covering the four-point plane).**

Lean statement: `D5/S3/Arith/Covering/BinaryCarryQuotient.plane_cover_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/BinaryCarryQuotient.plane_cover_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arbitrary active family of lines with nonzero binary normals covers the plane exactly when it contains a complementary parallel pair or a triple of distinct directions with even carry sum. Inactive indices impose no normal constraint.

There are two possible lines in each of the horizontal, vertical and diagonal directions. The four point-covering conditions select either a complementary pair or one of the four concurrent triples. Conversely, a complementary pair covers directly. For a distinct-direction triple, each coordinate of the normal sum is two; three failed line equations would have odd sum, contradicting the even carry sum.

**Theorem 1.5 (Exact descent with unchanged phases).**

Lean statement: `D5/S3/Arith/Covering/BinaryCarryQuotient.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/BinaryCarryQuotient.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer basepoint, all four lifts obtained by adding M times a binary pair are covered if and only if the quotient criterion holds. The criterion is invariant under adding M times any integer pair to the basepoint. Coverage of the square from zero inclusive to M exclusive by this criterion is equivalent both to original-row coverage of every integer pair and to original-row coverage of the period-N square.

On a lift, the scaled form changes by M times N/e times the normal dot the lift coordinates. An even N/e makes the row constant on the fiber. For odd N/e, coverage first requires activity; after division by M, the equation is the binary line equation with carry F/M modulo 2. Cancellation of M gives the stated pair and triple congruences. Reducing arbitrary integer lift coordinates modulo two proves representative invariance; Euclidean division supplies every basepoint in the finite quotient.

The theorem gives an equivalence for each fixed original phase assignment. It asserts no existence of a covering assignment. A compressed event whose next fiber is a point does not satisfy the line hypotheses automatically; a further descent requires a separate description of that event.

## References

- Truth anchor: `D5/S3/Arith/Covering/BinaryCarryQuotient.Criterion`
- Truth anchor: `D5/S3/Arith/Covering/BinaryCarryQuotient.covers`
- Truth anchor: `D5/S3/Arith/Covering/BinaryCarryQuotient.plane_cover_iff`
- Truth anchor: `D5/S3/Arith/Covering/BinaryCarryQuotient.result`
- Truth anchor: `D5/S3/Arith/Covering/BinaryCarryQuotient.scaled`
