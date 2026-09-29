# PathCurrentRegistrationTemplates

## Abstract

A dependent signature types one real statistic of a whole path in a signed state space with a peak.

**Definition 1.1 (Signed-peak path signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/PathCurrentRegistrationTemplates.signedPeakPathSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/PathCurrentRegistrationTemplates.signedPeakPathSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parameters are an arbitrary state type X, a real sign function on X, a peak state, two real profile values, a real normalizer and a natural horizon. States are whole paths N -> X. The sole role is Unit, and its output is one real number; the anchor type is Empty. Reg/D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent uses this signature with the forward-versus-reversed log-likelihood of the single-peak parity kernel as the actual readout. The definition is an operand for that source-bound registration, not a theorem or a registration proof.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/PathCurrentRegistrationTemplates.signedPeakPathSignature`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/DependentFamily](DependentFamily.md)
