# Kozaki–Kakei Conjecture 13

## Abstract

The allowable reorderings of the double-normalized even frieze matrices are exactly the rotations and reflections throughout the stated size range.

**Theorem 1.1 (The normalized action and the full level locus).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), 2 \le m \implies (\operatorname{Allowable}(m,s) \iff \operatorname{PreservesLevel}(s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConjecture13.allowable_iff_preservesLevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible matrix on the level has a unique ordered representative. Reordering transports matrix equivalence, so existence and uniqueness after reordering each normalized input is equivalent to preserving the written equality on all admissible inputs.

**Theorem 1.2 (Exact classification of allowable permutations).**

$$\forall m \in \mathbb{N},\; \left(2 \le m \land m \ne 3\right) \Rightarrow \left(\forall s \in \operatorname{Perm}\left(\operatorname{Fin}\left(2 m\right)\right),\; \operatorname{Allowable}\left(m, s\right) \Leftrightarrow \operatorname{Dihedral}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConjecture13.conjecture_13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuta Kozaki and Saburo Kakei (2026). *Coxeter Group Symmetries of Frieze Patterns*. DOI: [10.48550/arXiv.2611.25785](https://doi.org/10.48550/arXiv.2611.25785). URL: <https://arxiv.org/abs/2611.25785v1>.

*Commentary.*

Kozaki and Kakei, arXiv:2611.25785v1, section 3, printed page 9, Conjecture 13, identify the subgroup of the symmetric group whose reorderings admit the source normalization on every normalized input. Use columns zero through 2m−1 over the complex rational function field. A reordering uses the original column at σ(i) in position i. The normal form has first three columns (0,−1), (1,0), (1,1), all distinct-column minors nonzero, and every consecutive minor and D(1,2m) equal to one in one-based notation. The representative is unique under invertible left multiplication and invertible diagonal column rescaling. Dihedral permutations preserve the level by matching transport. In the reverse direction the constant-matrix bridge yields a scalar symmetry, and the signed four-column evaluation or the large-size support count recovers the cycle.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiConjecture13.allowable_iff_preservesLevel`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiConjecture13.conjecture_13`
- Dependency: [D5/S3/Geometry/KozakiKakeiFour](KozakiKakeiFour.md)
- Dependency: [D5/S3/Geometry/KozakiKakeiNormalization](KozakiKakeiNormalization.md)
- Dependency: [D5/S3/Geometry/KozakiKakeiPreservation](KozakiKakeiPreservation.md)
