# Quadratic Residues Modulo Four

## Abstract

Squares occupy only residues zero and one modulo four, obstructing residue three.

**Theorem 1.1 (Square residues and the two-square obstruction).**

$$\left(\forall n\in\mathbb{N},\ n^2\operatorname{mod}4\in\{0,1\}\right)\ \land\ \left(\forall a,b\in\mathbb{N},\ (a^2+b^2)\operatorname{mod}4\neq3\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/QuadraticResidues.square_residues_and_sum_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural square has residue zero or one modulo four. Consequently, the sum of two natural squares cannot have residue three modulo four.

Methodologically, the zeroth-layer refutation certificate is the R_4 reading: inspect the square image {0, 1}, then its pairwise-sum image {0, 1, 2}. This certificate explains the proof search but is not an additional clause of the formal theorem.

## References

- Truth anchor: `D5/S3/PrimeForms/QuadraticResidues.square_residues_and_sum_obstruction`
