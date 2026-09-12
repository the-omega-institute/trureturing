# Fubini–Study Angles and Recording Time

## Abstract

The Fubini–Study triangle inequality gives a recording-time bound under assumed speed bounds.

**Theorem 1.1 (The angle of the overlap modulus satisfies the triangle inequality).**

$$\Vert a \Vert=\Vert b \Vert=\Vert c \Vert=1 \Rightarrow \operatorname{arccos}(\Vert \langle a,c \rangle \Vert)\le\operatorname{arccos}(\Vert \langle a,b \rangle \Vert)+\operatorname{arccos}(\Vert \langle b,c \rangle \Vert)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/FubiniStudyRecordTime.fs_angle_triangle` (`✓ std3`). ∎

*Citation.* QuAIR Team (2026). *Angular geometry of purified distance*. URL: <https://github.com/QuAIR/Lean-QIT/blob/c1d59b133b56e3d79efb11ee46a728d290f761f5/QIT/States/Geometry/PurifiedDistanceAngle.lean>.

*Commentary.*

For unit vectors in any complex inner product space, the Fubini–Study angle is arccos of the modulus of their complex inner product. The two endpoint phases can be chosen so that their adjacent overlaps with the middle vector are real and nonnegative. The real-angle triangle inequality then bounds the unchanged endpoint overlap modulus.

This adapts QuAIR's finite-dimensional pure-vector proof. On vectors the angle is insensitive to phase; separation of points belongs to the space of rays. No quotient-space metric instance is constructed here.

**Theorem 1.2 (Orthogonal final records require contact time).**

$$\frac{\pi hbar}{4 E}\le\tau$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/FubiniStudyRecordTime.record_time_lower_bound` (`✓ std3`). ∎

*Citation.* QuAIR Team (2026). *Angular geometry of purified distance*. URL: <https://github.com/QuAIR/Lean-QIT/blob/c1d59b133b56e3d79efb11ee46a728d290f761f5/QIT/States/Geometry/PurifiedDistanceAngle.lean>.

*Commentary.*

Let a, m0 and m1 be unit vectors, with m0 and m1 orthogonal. Assume positive E and hbar, and assume that each endpoint's angle from the same initial vector a is at most E times tau divided by hbar. Their mutual angle is pi over two, so the triangle inequality yields the displayed lower bound.

The two displacement bounds are physical inputs. A speed hypothesis valid at every time supplies them by evaluation at the final time. This conditional theorem does not derive the Mandelstam–Tamm bound or model the Hamiltonian evolution.

**Theorem 1.3 (A total contact-time budget bounds the number of records).**

$$N\le\frac{4 E T}{\pi hbar}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/FubiniStudyRecordTime.record_count_upper_bound` (`✓ std3`). ∎

*Citation.* QuAIR Team (2026). *Angular geometry of purified distance*. URL: <https://github.com/QuAIR/Lean-QIT/blob/c1d59b133b56e3d79efb11ee46a728d290f761f5/QIT/States/Geometry/PurifiedDistanceAngle.lean>.

*Commentary.*

For N records, each pair of orthogonal final states has its own common initial state and the same positive E and hbar. Assume both displacement bounds for every record and that the sum of their contact durations is at most T. Summing the preceding time bound gives the count bound. The sum budget represents sequential, nonoverlapping contacts; it is an explicit assumption, not a conclusion about arbitrary parallel devices.

## References

- Truth anchor: `D5/S3/QuantumBounds/FubiniStudyRecordTime.fs_angle_triangle`
- Truth anchor: `D5/S3/QuantumBounds/FubiniStudyRecordTime.record_count_upper_bound`
- Truth anchor: `D5/S3/QuantumBounds/FubiniStudyRecordTime.record_time_lower_bound`
