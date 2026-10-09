# The signed triangle fan of a binary word

## Abstract

A binary word traces positive unit steps in one oriented plane. Signed triangle sums give area and centered first moments, including paths of zero signed area.

**Definition 1.1 (One ordered path).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(w\right) = \operatorname{Five}\left(\operatorname{q}\left(w\right).1, \operatorname{q}\left(w\right).2, 2\operatorname{A}\left(w\right), 12\operatorname{m}\left(w\right).1, 12\operatorname{m}\left(w\right).2\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/BinaryWordFan.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

True is the horizontal unit step and false is the vertical unit step. Prefix sums are the vertices of the path. Each consecutive pair contributes its determinant divided by two and that signed area times the sum of its vertices divided by three. The centered vector is the raw moment minus half the area times the endpoint. The five coordinates are the endpoint, twice the signed area, and twelve times each centered moment. No division by the total area occurs.

**Definition 1.2 (The update using old coordinates).**

$$\forall x \in Five,\; \forall c \in Bool,\; \operatorname{U}\left(x, c\right) = \operatorname{if}\left(c, \operatorname{Five}\left(x.u+1, x.v, x.d-x.v, x.e-3x.d-x.u \cdot x.v+x.v, x.f-x.v^{2}\right), \operatorname{Five}\left(x.u, x.v+1, x.d+x.u, x.e+x.u^{2}, x.f-3x.d+x.u \cdot x.v-x.u\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/BinaryWordFan.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All coordinates on the right are from the same old Five value. The true branch adds the horizontal unit step; the false branch adds the vertical unit step.

**Definition 1.3 (The common seam correction).**

$$\forall x \in Five,\; \forall y \in Five,\; \operatorname{star}\left(x, y\right) = \operatorname{Five}\left(x.u+y.u, x.v+y.v, x.d+y.d+(x.u \cdot y.v-x.v \cdot y.u), x.e+y.e+3(y.d \cdot x.u-x.d \cdot y.u)+(x.u \cdot y.v-x.v \cdot y.u)(x.u-y.u), x.f+y.f+3(y.d \cdot x.v-x.d \cdot y.v)+(x.u \cdot y.v-x.v \cdot y.u)(x.v-y.v)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/BinaryWordFan.star` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seam determinant is x.u times y.v minus x.v times y.u. The area and both moment corrections use this same determinant and the signed areas of the same two paths.

**Theorem 1.4 (Appending a supplied letter).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \forall c \in Bool,\; \operatorname{G}\left(\operatorname{append}\left(w, [c]\right)\right) = \operatorname{U}\left(\operatorname{G}\left(w\right), c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BinaryWordFan.G_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending a letter preserves the old vertices and adds their last triangle. The resulting arithmetic uses the old endpoint and old signed area. It is valid for the empty auxiliary word as well as every nonempty word.

**Theorem 1.5 (Concatenating two paths).**

$$\forall h \in \operatorname{List}\left(Bool\right),\; \forall k \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(\operatorname{append}\left(h, k\right)\right) = \operatorname{star}\left(\operatorname{G}\left(h\right), \operatorname{G}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BinaryWordFan.G_concat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five coordinates of a concatenation satisfy the signed fan concatenation formula. Both moment coordinates include the endpoint and signed-area seam terms of the same two paths.

**Theorem 1.6 (Reversing the complete word).**

$$\forall w \in \operatorname{List}\left(Bool\right),\; \operatorname{G}\left(\operatorname{reverse}\left(w\right)\right) = \operatorname{Five}\left(\operatorname{G}\left(w\right).u, \operatorname{G}\left(w\right).v, -\operatorname{G}\left(w\right).d, \operatorname{G}\left(w\right).e, \operatorname{G}\left(w\right).f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/BinaryWordFan.G_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversal fixes both letter counts, negates signed area, and preserves both centered moment coordinates. This statement compares mathematical positive words in a common unit reference. It supplies no operation, acquisition, calibration, or reversal authority over a physical source.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/BinaryWordFan.G`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BinaryWordFan.G_append`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BinaryWordFan.G_concat`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BinaryWordFan.G_reverse`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BinaryWordFan.U`
- Truth anchor: `D5/S3/Combinatorics/Partitions/BinaryWordFan.star`
