# A Critical Coset Obstruction for Thirty-Three Congruence Rows

## Abstract

Thirty-three fixed congruence rows leave at least twelve holes on every critical coset, uniformly in their original integer phases.

**Definition 1.1 (The original rows).**

Lean statement: `D5/S3/Arith/Covering/CriticalCosetObstruction.rowCovers`

*Formalization.* `D5/S3/Arith/Covering/CriticalCosetObstruction.rowCovers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function rows contains the literal prime, modulus, and two integer coefficients of each of the 33 selected rows. Row i covers z precisely when its modulus divides a_i z_1 + b_i z_2 - c_i. The phase vector c is fixed before varying z. Integer phases include negative and large representatives. The constants are Q = 16865820972000 and B = 733296564000, with Q = 23B and 23 not dividing B.

**Definition 1.2 (The active affine lines).**

Lean statement: `D5/S3/Arith/Covering/CriticalCosetObstruction.fieldHoles`

*Formalization.* `D5/S3/Arith/Covering/CriticalCosetObstruction.fieldHoles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over the field with 23 elements, a hole avoids every active line a_i x + b_i y = offset_i. The active set is arbitrary, including empty, and every offset is arbitrary. All normals come from the original rows.

**Theorem 1.3 (Twelve holes for every affine translation).**

Lean statement: `D5/S3/Arith/Covering/CriticalCosetObstruction.affine_holes`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/CriticalCosetObstruction.affine_holes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the 33 homogeneous linear forms has coefficient 1 at X^22 Y^11. Subtracting arbitrary constants from the factors changes only terms of total degree at most 32. The Combinatorial Nullstellensatz therefore gives a nonzero value over all 23 x-values and any set of at least 12 y-values. If there were at most 11 holes, at least 12 y-values would be absent from their projection, a contradiction. Discarding inactive lines preserves the bound.

**Definition 1.4 (Distinct uncovered coset residues).**

Lean statement: `D5/S3/Arith/Covering/CriticalCosetObstruction.cosetHoles`

*Formalization.* `D5/S3/Arith/Covering/CriticalCosetObstruction.cosetHoles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lift (x,y) to w + B(x,y) using field representatives and reduce modulo Q. This map is injective, so its domain gives 529 distinct coset residues. The counted holes avoid both the original union and its translate by (Q/2,0). Each row modulus divides Q/2, so the paired translate does not supply an independent second line.

**Definition 1.5 (The retained-predicate interface).**

Lean statement: `D5/S3/Arith/Covering/CriticalCosetObstruction.BPeriodic`

*Formalization.* `D5/S3/Arith/Covering/CriticalCosetObstruction.BPeriodic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A predicate U on integer pairs is B-periodic when every translation by B times an integer pair preserves its truth value.

**Definition 1.6 (The repair hypothesis).**

Lean statement: `D5/S3/Arith/Covering/CriticalCosetObstruction.claim`

*Formalization.* `D5/S3/Arith/Covering/CriticalCosetObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hypothesis asserts that one original phase vector and one coset leave fewer than twelve paired holes, or that one B-periodic U fails globally while adjoining these same rows makes it true everywhere.

**Theorem 1.7 (The repair hypothesis is false).**

Lean statement: `D5/S3/Arith/Covering/CriticalCosetObstruction.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/CriticalCosetObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write e_i = 23m_i. On the coset at w, a row is active exactly when m_i divides c_i - a_i w_1 - b_i w_2. Its field offset is the integer quotient of this carry by m_i, multiplied by the inverse of B/m_i modulo 23. The exact equivalence holds for all integer coordinates, including shifted representatives. The affine bound gives at least twelve distinct paired holes for every w and c. A hole on a coset where U fails contradicts any proposed global repair. Consequently, for each fixed c and B-periodic U, global truth of U or the removed rows is equivalent to global truth of U. The specific retained 244-phase rescue predicate, its ternary and stable branches, and its B-periodicity are not encoded here. This result does not assert a full 277-to-244 rescue equivalence, a 285-row cover, or a solution of Erdos problem 203.

## References

- Truth anchor: `D5/S3/Arith/Covering/CriticalCosetObstruction.BPeriodic`
- Truth anchor: `D5/S3/Arith/Covering/CriticalCosetObstruction.affine_holes`
- Truth anchor: `D5/S3/Arith/Covering/CriticalCosetObstruction.claim`
- Truth anchor: `D5/S3/Arith/Covering/CriticalCosetObstruction.cosetHoles`
- Truth anchor: `D5/S3/Arith/Covering/CriticalCosetObstruction.fieldHoles`
- Truth anchor: `D5/S3/Arith/Covering/CriticalCosetObstruction.result`
- Truth anchor: `D5/S3/Arith/Covering/CriticalCosetObstruction.rowCovers`
