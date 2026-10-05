# Fixed Collision Exceptions

## Abstract

In a distinct odd cover with no modulus divisible by 27, minimality of the modulus sum at its class count forces at most two fixed originals to meet every ordinary-prime collision at a fixed modulo-9 word and modulo-5 root.

**Definition 1.1 (Originals at a fixed word and root).**

Lean statement: `D5/S3/Arith/Covering/FixedCollisionExceptions.collisionTop`

*Formalization.* `D5/S3/Arith/Covering/FixedCollisionExceptions.collisionTop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An original belongs to the selected group when its modulus is divisible by 45, its residue agrees with u modulo 9, and its residue agrees with omega modulo 5. Every positive five depth is included, with all other prime factors retained.

**Definition 1.2 (Literal prime collisions).**

Lean statement: `D5/S3/Arith/Covering/FixedCollisionExceptions.ordinaryPrimeCollision`

*Formalization.* `D5/S3/Arith/Covering/FixedCollisionExceptions.ordinaryPrimeCollision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two distinct original labels collide when some prime other than 3 and 5 divides both moduli and their actual residues agree modulo that prime. This condition does not require a point in the intersection of their full congruence classes.

**Theorem 1.3 (A four-slot replacement excludes disjoint collisions).**

Lean statement: `D5/S3/Arith/Covering/FixedCollisionExceptions.no_disjoint_ordinary_prime_collisions`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/FixedCollisionExceptions.no_disjoint_ordinary_prime_collisions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F cover every natural number with L congruence classes of pairwise distinct odd moduli greater than one. Suppose no modulus is divisible by 27, and the sum of its moduli is minimal among all such covers with L classes. The comparison covers have no restriction on prime heights. Then four distinct originals in one selected group cannot form two disjoint prime-collision pairs.

For collision primes p and r that differ, replace the four originals by classes of moduli 27, 135, 27p and 27r. The three extensions of u modulo 27 assign the first two rows, or select a final row using the actual prime phase of the appropriate original pair.

If the collision primes coincide, use moduli 27, 135, 27p and 135p. The phases of the two collision pairs may differ. In both cases every point of every removed congruence class lies in a replacement class. All other originals are retained, and divisibility by 27 makes all four new moduli globally fresh.

For distinct p and r the old four-modulus sum is at least 90(p+r), while the new sum is 27(6+p+r). For equal primes, distinct positive multiples of 45p give an old sum of at least 225p, while the new sum is 162(1+p). Each replacement strictly lowers the sum without changing L, contradicting minimality.

**Theorem 1.4 (One exception set works for every source point).**

Lean statement: `D5/S3/Arith/Covering/FixedCollisionExceptions.exists_fixed_collision_exceptions`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/FixedCollisionExceptions.exists_fixed_collision_exceptions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same assumptions, for every u and omega there is a set X of at most two original labels in the selected group such that no two labels outside X have an ordinary-prime collision. If a collision exists, its two endpoints form X; otherwise X is empty.

The choice of X precedes every cofactor point and probability law. Its labels remain in the original cover. The theorem does not assume minimal class count, does not restrict five depths, and does not assert noncoverage for arbitrary odd distinct families.

## References

- Truth anchor: `D5/S3/Arith/Covering/FixedCollisionExceptions.collisionTop`
- Truth anchor: `D5/S3/Arith/Covering/FixedCollisionExceptions.exists_fixed_collision_exceptions`
- Truth anchor: `D5/S3/Arith/Covering/FixedCollisionExceptions.no_disjoint_ordinary_prime_collisions`
- Truth anchor: `D5/S3/Arith/Covering/FixedCollisionExceptions.ordinaryPrimeCollision`
