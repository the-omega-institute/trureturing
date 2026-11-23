# Character projection in the theta quotient

## Abstract

Character projection in the theta quotient.

**Theorem 1.1 (The projector lands in character four).**

Lean statement: `D5/S3/Arith/Partitions/BilgiciThetaGrading.T_P`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Partitions/BilgiciThetaGrading.T_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Göksal Bilgici (2026). *Nine-Colored Partition Components Modulo 19*. DOI: [10.48550/arXiv.2611.24516](https://doi.org/10.48550/arXiv.2611.24516). URL: <https://arxiv.org/html/2611.24516v1#S8.I1.i1>.

*Commentary.*

The nine signed doubling iterates define a linear projector. Shifting the index in the sum multiplies it by four.

**Theorem 1.2 (Projected homogeneous representatives).**

Lean statement: `D5/S3/Arith/Partitions/BilgiciThetaGrading.eigengrade_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Partitions/BilgiciThetaGrading.eigengrade_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Göksal Bilgici (2026). *Nine-Colored Partition Components Modulo 19*. DOI: [10.48550/arXiv.2611.24516](https://doi.org/10.48550/arXiv.2611.24516). URL: <https://arxiv.org/html/2611.24516v1#S8.I1.i1>.

*Commentary.*

In centered degree and weight the image of the projected homogeneous subspace is exactly the doubling eigenspace inside that quotient grade.

**Theorem 1.3 (Signed field relations descend to zero).**

Lean statement: `D5/S3/Arith/Partitions/BilgiciThetaGrading.theta_annihilated`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Partitions/BilgiciThetaGrading.theta_annihilated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Göksal Bilgici (2026). *Nine-Colored Partition Components Modulo 19*. DOI: [10.48550/arXiv.2611.24516](https://doi.org/10.48550/arXiv.2611.24516). URL: <https://arxiv.org/html/2611.24516v1#S8.I1.i1>.

*Commentary.*

The signed integer indices give a field-indexed re-pairing relation. Its projected class vanishes in the global theta quotient.

## References

- Truth anchor: `D5/S3/Arith/Partitions/BilgiciThetaGrading.T_P`
- Truth anchor: `D5/S3/Arith/Partitions/BilgiciThetaGrading.eigengrade_exact`
- Truth anchor: `D5/S3/Arith/Partitions/BilgiciThetaGrading.theta_annihilated`
- Dependency: [D5/S3/Arith/Partitions/BilgiciThetaQuartic](BilgiciThetaQuartic.md)
