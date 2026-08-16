# Exact Second-Order Transcription

## Abstract

The exact T0 substitution yields the closed second-order golden-radical value.

**Theorem 1.1 (The second-order transcription has an exact closed form).**

$$(1-\sqrt{5})T_{0}+\frac{15\sqrt{5}-33}{8}=\frac{5\sqrt{5}-7}{24}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Transcription/PhiSecondTranscription.phi_second_transcription_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here T0 is the deposited exact Sturmian-Dirichlet value (27 - 13 sqrt(5)) / 24. Substitution reduces the statement to the standard identity sqrt(5)^2 = 5.

This theorem covers only the source's exact second-order transcription clause; it makes no claim about the surrounding reconstruction program or numerical certificates.

## References

- Truth anchor: `D5/S3/Constants/Transcription/PhiSecondTranscription.phi_second_transcription_exact`
- Dependency: [D5/S3/Constants/SturmianDirichletValue](../SturmianDirichletValue.md)
