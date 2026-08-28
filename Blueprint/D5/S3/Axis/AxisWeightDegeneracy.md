# Axis Weight Degeneracy

## Abstract

Consecutive axis weights coincide exactly on the diagonal of the two readings.

The axis weight reads a pair of parameters at the two Galois embeddings and raises each to the depth. Both the golden ratio and its conjugate satisfy the same quadratic, so each drops its square by exactly one unit of itself, and the first step of the tower compares the two readings against each other and nothing else.

The consequence is that depth zero and depth one carry the same weight precisely when the two readings agree. The locus is a line, not a point, and it contains readings that are in no sense degenerate.

This module exists as an erratum. The prose attached to the depth-zero evaluation in the trace recurrence asserts that consecutive depths never carry the same weight except under a trivial reading. That assertion is not proved by the theorem it is attached to, and it is false. The frozen module is left byte-identical; the correction is carried here as a stronger statement naming the exact locus, so the false sentence is closed by a truth rather than by a deletion.

**Lemma 1.1 (Both embeddings drop their square by one unit).**

$$\mathit{phi}^{2} - \mathit{phi} = 1 \land \mathit{psi}^{2} - \mathit{psi} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisWeightDegeneracy.sq_sub_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the two roots of the golden quadratic satisfies the same identity, which is the single fact the degeneracy computation needs at both embeddings.

**Theorem 1.2 (The first weight step degenerates exactly on the diagonal).**

$$\forall x \in R, y \in R,\; \operatorname{axisWeight}\left(x, y, 0\right) = \operatorname{axisWeight}\left(x, y, 1\right) \Leftrightarrow x = y$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisWeightDegeneracy.axisWeight_zero_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cancelling the exponential and substituting the quadratic on both embeddings leaves the difference of the two readings, so the weights agree if and only if those readings agree.

**Lemma 1.3 (Degeneracy occurs away from any trivial reading).**

$$\operatorname{axisWeight}\left(1, 1, 0\right) = \operatorname{axisWeight}\left(1, 1, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisWeightDegeneracy.degeneracy_occurs_off_the_trivial_reading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking both readings equal to one exhibits a coincidence of consecutive weights at a reading that is not trivial, which is the counterexample the erratum carries.

**Lemma 1.4 (Off the diagonal consecutive weights differ).**

$$\forall x \in R, y \in R,\; x \ne y \Rightarrow \operatorname{axisWeight}\left(x, y, 0\right) \ne \operatorname{axisWeight}\left(x, y, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisWeightDegeneracy.axisWeight_zero_ne_one_off_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coincidence is confined to the diagonal: whenever the two readings differ, so do the weights at the first two depths.

**Theorem 1.5 (The degeneracy locus packaged).**

$$\left(\forall x \in R, y \in R,\; \operatorname{axisWeight}\left(x, y, 0\right) = \operatorname{axisWeight}\left(x, y, 1\right) \Leftrightarrow x = y\right) \land \left(\operatorname{axisWeight}\left(1, 1, 0\right) = \operatorname{axisWeight}\left(1, 1, 1\right) \land \left(\forall x \in R, y \in R,\; x \ne y \Rightarrow \operatorname{axisWeight}\left(x, y, 0\right) \ne \operatorname{axisWeight}\left(x, y, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisWeightDegeneracy.axis_weight_degeneracy_locus_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One conjunction carrying the correction: degeneracy holds exactly on the diagonal, it is attained at a nontrivial reading, and it fails everywhere off that line.

## References

- Truth anchor: `D5/S3/Axis/AxisWeightDegeneracy.axisWeight_zero_eq_one_iff`
- Truth anchor: `D5/S3/Axis/AxisWeightDegeneracy.axisWeight_zero_ne_one_off_diagonal`
- Truth anchor: `D5/S3/Axis/AxisWeightDegeneracy.axis_weight_degeneracy_locus_package`
- Truth anchor: `D5/S3/Axis/AxisWeightDegeneracy.degeneracy_occurs_off_the_trivial_reading`
- Truth anchor: `D5/S3/Axis/AxisWeightDegeneracy.sq_sub_self`
- Dependency: [D5/S3/Axis/AxisTraceRecurrence](AxisTraceRecurrence.md)
