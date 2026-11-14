# Two-Anchor Gram Corridor

## Abstract

Two-anchor Gram determinants give the squared corridor area and detect independence.

**Definition 1.1 (The two-anchor Gram matrix).**

Lean statement: `D5/S3/QuantumContext/TwoAnchorGram.twoAnchorGram`

*Formalization.* `D5/S3/QuantumContext/TwoAnchorGram.twoAnchorGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For vectors u and v in a real inner-product space, twoAnchorGram u v is the 2 by 2 Gram matrix built from the vector family [u, v].

**Theorem 1.2 (The two-anchor Gram determinant formula).**

$$\forall E: \operatorname{Type}*, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], \forall u: E, \forall v: E, \operatorname{det}\left(\operatorname{twoAnchorGram}\left(u, v\right)\right) = \operatorname{norm}(u)^{2} \cdot \operatorname{norm}(v)^{2} - (\operatorname{realInner}\left(u, v\right)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/TwoAnchorGram.two_anchor_gram_det_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the two-anchor Gram matrix is the squared area expression ‖u‖²‖v‖² − ⟪u,v⟫². This is the exact algebraic quantity used for the chapter's two-anchor compatibility corridor.

**Theorem 1.3 (Positive Gram area is equivalent to independent anchors).**

Lean statement: `D5/S3/QuantumContext/TwoAnchorGram.two_anchor_gram_det_pos_iff`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/TwoAnchorGram.two_anchor_gram_det_pos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant is strictly positive exactly when the two vectors are linearly independent over ℝ. Thus the compatibility corridor has positive area precisely away from the collinear boundary.

## References

- Truth anchor: `D5/S3/QuantumContext/TwoAnchorGram.twoAnchorGram`
- Truth anchor: `D5/S3/QuantumContext/TwoAnchorGram.two_anchor_gram_det_formula`
- Truth anchor: `D5/S3/QuantumContext/TwoAnchorGram.two_anchor_gram_det_pos_iff`
