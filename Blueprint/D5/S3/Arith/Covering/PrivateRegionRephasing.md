# Private Region Rephasing

## Abstract

In a distinct odd cover with the fewest possible classes, two descendants sharing a residue modulo an original modulus force every odd nonunit modulus enclosing that original class's complete private region to occur.

**Theorem 1.1 (Crowded descendants force an enclosure modulus).**

Lean statement: `D5/S3/Arith/Covering/PrivateRegionRephasing.crowded_descendants_force_private_encloser`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrivateRegionRephasing.crowded_descendants_force_private_encloser` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F cover every natural number by L congruence classes with pairwise distinct odd moduli greater than one. Assume L is no larger than the number of classes in any such cover. Choose three distinct original classes g, i and j. Suppose the modulus of g divides the moduli of both i and j, and the residues of i and j agree modulo the modulus of g.

Let e be odd and greater than one, and let w be a natural number. If every private point of g is congruent to w modulo e, then e is one of F's original moduli. A private point of g belongs to its congruence class and to no other original class. The hypothesis concerns all such points. The conclusion permits e to equal the modulus of g and does not assert an increase of the original modulus inventory.

Suppose e is absent. Replace class i by the class with residue w modulo e, and change the residue of g to that of i while keeping its modulus. The replacement covers every private point of g. Every other point has an original owner other than g. If this owner is i or j, the changed class g covers the point; otherwise its original owner is unchanged. Thus the new family covers without using j. Absence of e preserves distinct moduli, and deleting j contradicts the minimal number of classes.

## References

- Truth anchor: `D5/S3/Arith/Covering/PrivateRegionRephasing.crowded_descendants_force_private_encloser`
- Dependency: [D5/S3/Arith/Covering/ConcentratedPrimeSingleton](ConcentratedPrimeSingleton.md)
