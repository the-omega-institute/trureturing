# Unit-Circle Diameter Geometry

## Abstract

Angular estimates for chains of unit vectors and chord bounds for finite unit-circle sets.

**Lemma 1.1 (A common supporting line from a diameter pair).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.circle_diameter_halfPlane`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.circle_diameter_halfPlane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Commentary.*

Take two unit complex numbers p and q with distance less than √3. There is a common unit phase and a positive real threshold t with t squared equal to one minus one quarter of the squared chord length. Every unit point within that chord length of both endpoints has real part at least t after the same rotation. For a spectrum, the two distance hypotheses follow by taking a pair that attains its diameter.

**Lemma 1.2 (Endpoint chord for a chain with small increments).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.finset_unit_chord_lt_sqrt_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.finset_unit_chord_lt_sqrt_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Commentary.*

Consider an insertion chain of unit vectors. When the chord of each step has an upper bound at most one, the angle of that step is at most π/3 times its chord bound. A total of those bounds strictly below two forces the endpoint chord to be shorter than √3.

**Lemma 1.3 (A supporting line at the nearest point of the convex hull).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.unitCircle_halfPlane_with_chord_of_zero_not_mem_convexHull`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.unitCircle_halfPlane_with_chord_of_zero_not_mem_convexHull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sergey Bravyi, Natalie Parham and Minh Tran (2026). *Identity Check Problem for Shallow Quantum Circuits*. DOI: [10.4230/LIPIcs.ITCS.2026.27](https://doi.org/10.4230/LIPIcs.ITCS.2026.27). URL: <https://doi.org/10.4230/LIPIcs.ITCS.2026.27>.

*Commentary.*

For a nonempty finite set on the unit circle whose convex hull excludes zero, the nearest point of the hull to zero gives a positive supporting threshold t after a common rotation. The set contains two points with chord length 2√(1−t²), with coincident endpoints permitted when t is one.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.circle_diameter_halfPlane`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.finset_unit_chord_lt_sqrt_three`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/SpectrumGeometry.unitCircle_halfPlane_with_chord_of_zero_not_mem_convexHull`
