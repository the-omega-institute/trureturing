# SixRowPhysicalExtraction

## Abstract

Actual six-row APPT supplies every physical scalar constraint on one original spectrum

**Theorem 1.1 (literal APPT physical extraction).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalExtraction.literal_physical`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalExtraction.literal_physical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least 23, start with an ordered, nonnegative, unit-mass spectrum l and APPT of its diagonal in the supplied product labelling. Set U=l[6n-21], B=l[14], r=(B-U)/U, h_i=(l[i]-B)/U for the first fifteen slots, and d_j=(U-l[6n-21+j])/U for the last twenty-one. Literal moments give U>0 and the two actual zero slots h_14=d_0=0. The coupling of the same l and labelling gives the squared coupled inequality. The slack and head cap agree with their scalar definitions. This yields PhysicalScalarHyp r H D a q on the sums and squared sums of those same lists, including a>=0 and the zero-slot Cauchy bounds H^2/14<=a and D^2/20<=q.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalExtraction.literal_physical`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling](SixRowCoupling.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalMoments](SixRowPhysicalMoments.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData](SixRowScalarData.md)
