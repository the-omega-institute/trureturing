# Exact Dual-Lattice Formula

## Abstract

The dual lattice of Lambda^2 A4 is exactly its one-fifth Hodge image.

**Theorem 1.1 (The dual lattice is the one-fifth Hodge image).**

$$dualLattice = oneFifthHodgeLattice$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/ExactDualLatticeFormula.dual_lattice_eq_one_fifth_hodge_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lattice L is the integer span of the chosen ordered basis of the real scalar extension of Lambda^2 A4. Its Gram pairing is defined by the displayed six-by-six matrix G. The left-hand side dualLattice consists exactly of the real vectors whose Gram pairing with every vector of L lies in the embedded integer submodule.

The right-hand side oneFifthHodgeLattice is the image of every vector of L under the endomorphism represented by J divided by five. Thus the statement is an equality of integral submodules, not merely an equality of determinants, ranks, or cardinalities.

Pinned Mathlib supplies the exact structural theorem that the dual of the integer span of a basis is the integer span of its bilinear dual basis. The local calculation proves that G is nondegenerate and that the six J-over-five basis images are a signed permutation of that dual basis. Signed permutation preserves the complete integer span, yielding the displayed submodule equality without hypotheses.

## References

- Truth anchor: `D5/S3/Arith/Lattices/ExactDualLatticeFormula.dual_lattice_eq_one_fifth_hodge_lattice`
