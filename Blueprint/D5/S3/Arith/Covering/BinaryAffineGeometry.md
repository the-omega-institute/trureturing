# Mixed affine covers of the binary plane

## Abstract

Binary affine sets cover the plane exactly through six minimal configurations.

The points are pairs of binary coordinates. The three nonzero linear forms are x, y and x plus y. An affine shape is empty, the full plane, a level set of one of these forms, or a single point.

**Definition 1.1 (The six alternatives).**

Lean statement: `D5/S3/Arith/Covering/BinaryAffineGeometry.Alternatives`

*Formalization.* `D5/S3/Arith/Covering/BinaryAffineGeometry.Alternatives` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let F indicate availability of the full plane, L indicate availability of each line, and P indicate availability of each singleton. The alternatives are: F; a complementary parallel pair; the three lines through one point; two distinct directions with their unique missing singleton; a line with both complementary singletons; or all four singletons. These availabilities may be existential predicates over an arbitrary indexed family.

**Definition 1.2 (Minimality by private points).**

Lean statement: `D5/S3/Arith/Covering/BinaryAffineGeometry.MinimalCover`

*Formalization.* `D5/S3/Arith/Covering/BinaryAffineGeometry.MinimalCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite family is a minimal cover when it covers every point and each member has a point that belongs to no other member. Removing that member therefore leaves a hole. The pattern family uses the omitted direction to label an unordered pair of distinct directions exactly once.

**Theorem 1.3 (Complete mixed-cover identity).**

Lean statement: `D5/S3/Arith/Covering/BinaryAffineGeometry.mixed_cover_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/BinaryAffineGeometry.mixed_cover_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point is covered by an available full plane, line or singleton if and only if one of the six alternatives holds. There are twenty-seven distinct patterns; their shape families are distinct and every pattern is minimal. The six counts are respectively one, three, four, twelve, six and one. Empty sets contribute nothing and repeated events do not change availability.

If the lines alone cover, the binary line-cover identity gives a parallel pair or a concurrent triple. Otherwise take a point missed by every line. Two line directions together miss only that point, so its singleton supplies the remaining part. With just one direction and no parallel pair, a line needs its two complementary singletons. Without any lines, all four singletons are necessary. Conversely each listed configuration covers directly; private points establish minimality.

## References

- Truth anchor: `D5/S3/Arith/Covering/BinaryAffineGeometry.Alternatives`
- Truth anchor: `D5/S3/Arith/Covering/BinaryAffineGeometry.MinimalCover`
- Truth anchor: `D5/S3/Arith/Covering/BinaryAffineGeometry.mixed_cover_iff`
- Dependency: [D5/S3/Arith/Covering/BinaryCarryQuotient](BinaryCarryQuotient.md)
