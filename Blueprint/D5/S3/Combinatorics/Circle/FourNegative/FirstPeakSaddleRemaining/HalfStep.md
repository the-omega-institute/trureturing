# The c>=3, a>c+d region

## Abstract

Half-step interpolation and native selection

**Lemma 1.1 (Interpolate in r and then h).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_interpolate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_interpolate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

HalfCorners contains one negative corner, four positive rectangle corners and the boundary case. The three certificate modules cover K>=4, F>=4 or K,F>=2. half_interpolate uses the explicit separate affine identities in r and h, with no hr term; half_floor_split chooses a positive r even at exact multiples.

**Lemma 1.2 (Construct masks above the diagonal).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_step_choice_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_step_choice_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>b>d>c>=3, a>c+d and b<=c+d, set K=2^(b-d-1), F=2^(c+d-b), e=2^(a-c-d-1), so z=2KF and J=Fe. Dyadic parameter cases select one of the three certificate regions. half_arithmetic assembles the residue choice and margins, then native_of_selection gives NativeChoice. No extra grain restriction is a theorem hypothesis.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_interpolate`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_step_choice_exists`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfBothCertificates](HalfBothCertificates.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfF4Certificates](HalfF4Certificates.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfK4Certificates](HalfK4Certificates.md)
