# Three-Anchor Gram Corridor

## Abstract

Three-anchor Gram determinants give the squared volume expression and detect independence.

**Definition 1.1 (The three-anchor Gram matrix).**

Lean statement: `D5/S3/QuantumContext/ThreeAnchorGram.threeAnchorGram`

*Formalization.* `D5/S3/QuantumContext/ThreeAnchorGram.threeAnchorGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For vectors u, v, and w in a real inner-product space, threeAnchorGram u v w is the 3 by 3 Gram matrix built from the vector family [u, v, w].

**Theorem 1.2 (The three-anchor Gram determinant formula).**

$$\forall E: \operatorname{Type}*, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], \forall u: E, \forall v: E, \forall w: E, \operatorname{det}\left(\operatorname{threeAnchorGram}\left(u, v, w\right)\right) = (\operatorname{norm}(u)^{2}) \cdot (\operatorname{norm}(v)^{2}) \cdot (\operatorname{norm}(w)^{2}) + 2 \cdot \operatorname{realInner}\left(u, v\right) \cdot \operatorname{realInner}\left(u, w\right) \cdot \operatorname{realInner}\left(v, w\right) - (\operatorname{norm}(u)^{2}) \cdot (\operatorname{realInner}\left(v, w\right)^{2}) - (\operatorname{norm}(v)^{2}) \cdot (\operatorname{realInner}\left(u, w\right)^{2}) - (\operatorname{norm}(w)^{2}) \cdot (\operatorname{realInner}\left(u, v\right)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ThreeAnchorGram.three_anchor_gram_det_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant of the three-anchor Gram matrix is the squared volume expression obtained by expanding the 3 by 3 determinant.

**Theorem 1.3 (Positive Gram volume is equivalent to independent anchors).**

Lean statement: `D5/S3/QuantumContext/ThreeAnchorGram.three_anchor_gram_det_pos_iff`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ThreeAnchorGram.three_anchor_gram_det_pos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant is strictly positive exactly when the three vectors are linearly independent over ℝ. Thus the three-anchor compatibility volume is positive precisely away from the dependent boundary.

## References

- Truth anchor: `D5/S3/QuantumContext/ThreeAnchorGram.threeAnchorGram`
- Truth anchor: `D5/S3/QuantumContext/ThreeAnchorGram.three_anchor_gram_det_formula`
- Truth anchor: `D5/S3/QuantumContext/ThreeAnchorGram.three_anchor_gram_det_pos_iff`
