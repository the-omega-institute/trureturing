# Prime Cuts from Fresh Ternary Repairs

## Abstract

A globally minimal distinct odd cover bounds every selected prime cut by the number of its actually used tags.

**Theorem 1.1 (One fan covers all matching pairs).**

Lean statement: `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.ternary_prime_fan_covers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.ternary_prime_fan_covers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any natural height h and old residue u. Put D = 3^h and N = 3D. Let S and T be finite tag sets, each tag coprime to N, and let phase(p) be one fixed residue for each tag. The new labels are N and Np for every indexed tag on the two sides. Their residues can be chosen simultaneously so that every natural x with old word u and matching roots at some p in S and t in T belongs to a new class.

The next ternary digit selects the class. Digit zero uses residue u modulo D in the pure N class. Digit one uses CRT to combine the next word with phase(p); digit two uses phase(t). All pairs use the same class for a fixed tag on a fixed side. No common point of all matching-pair regions is required. The covering statement itself permits overlapping tag sets; distinctness of the new labels is a separate requirement for replacing a distinct cover.

**Theorem 1.2 (A smaller fresh repair contradicts minimality).**

Lean statement: `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.fresh_finite_replacement_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.fresh_finite_replacement_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F cover all natural numbers by L congruence classes of distinct odd moduli greater than one. Assume L is minimal among all such covers, and the modulus sum of F is minimal among those with L classes. Select any finite family of distinct original indices. A finite family of distinct odd nonunit moduli, fresh against every original modulus, cannot cover every removed class while using no more classes and a strictly smaller modulus sum. Retain the unselected originals and insert the fresh family. Cardinality minimality forces equal total cardinality, and reindexing then contradicts sum minimality. Neither comparison domain restricts prime heights.

**Theorem 1.3 (Selected originals are bounded by used tags).**

Lean statement: `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.selected_prime_cut_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.selected_prime_cut_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In such a globally minimal cover, fix any h, any q at least seven, and one old word u modulo D = 3^h. Suppose no original modulus is divisible by 3D. Let I be any finite family injected into the original indices, with actual modulus D q m(i) and residue u modulo D at each selected index. Choose prime tags left(i) and right(i) dividing m(i). Each selected original residue must match the same literal phase(p) at each chosen tag p. Require the images of left and right to be disjoint.

Then the cardinality of I is at most the sum of the cardinalities of those two images. The tags are odd because they divide the actual odd moduli, and the original height bound excludes the tag three. Disjointness makes each selected pair distinct and makes all new labels distinct. Divisibility by 3D makes every new label fresh. The fan covers each complete removed congruence class, not only a chosen private point or a phase sample.

Write V for the number of used tags and M for the sum of m(i). The sum of the used tags is at most the sum of left(i)+right(i), which is at most M: distinct prime divisors have product dividing m(i), and their product dominates their sum. If |I| exceeds V, the fan uses 1+V classes, no more than |I|, and has cost at most 3D(1+M), strictly smaller than DqM. The preceding finite replacement theorem excludes this case.

Empty selected families and height zero are included. Primality of q, a shared residue modulo q, and simultaneous matching of all cofactor coordinates are not assumptions. Selecting any subfamily and its actually used tags is permitted, which is the input needed for hereditary cut bounds. The conclusion alone does not assert existence or nonexistence of distinct odd covers.

## References

- Truth anchor: `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.fresh_finite_replacement_descent`
- Truth anchor: `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.selected_prime_cut_card_le`
- Truth anchor: `D5/S3/Arith/Covering/PrimeCutOwnerCapacity.ternary_prime_fan_covers`
