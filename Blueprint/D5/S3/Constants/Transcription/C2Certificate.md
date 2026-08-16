# Second-Coefficient Transcription Certificate

## Abstract

The registered second coefficient satisfies its transcription and error certificates.

**Theorem 1.1 (The second-coefficient transcription is certified).**

$$c_2=\frac{\sqrt{5}-1}{2}B_h+(3-\frac{7\sqrt{5}}{2})T_0+3\sqrt{5}T_1+\frac{269\sqrt{5}-623}{48}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Transcription/C2Certificate.c2_transcription_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact equality unfolds the frozen catalog definition. Rational enclosures of the positive square root of five certify the stated input and output error bars.

The same bounds show that replacing the registered zero-moment center by its corrected closed form shifts the coefficient by less than the declared error. They also exclude the four recorded candidate values; the logarithmic exclusion uses the standard strict logarithm bound and the lower bound three for pi.

## References

- Truth anchor: `D5/S3/Constants/Transcription/C2Certificate.c2_transcription_certificate`
