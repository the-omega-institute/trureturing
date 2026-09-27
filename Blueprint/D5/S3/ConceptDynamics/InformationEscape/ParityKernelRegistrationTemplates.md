# ParityKernelRegistrationTemplates

## Abstract

Dependent signatures type the coordinate-record law and the step-indexed path functionals of parity kernels.

**Definition 1.1 (Coordinate-record signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates.subcoordinateRecordSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates.subcoordinateRecordSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parameters are a dimension d, a real profile on the sign hypercube of dimension d, a set of coordinates and a natural horizon T. States are sequences of T + 1 sign vectors. The sole role is Unit with one real output; the anchor type is Empty. Reg/D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates uses it with the coordinate-record law as the actual readout. The definition is an operand for that source-bound registration, not a theorem or a registration proof.

**Definition 1.2 (Profile-pair step signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates.profilePairStepSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates.profilePairStepSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parameters are a dimension d and two real profiles on the sign hypercube. States are path lengths s. The sole role is Unit with one real output; the anchor type is Empty. Reg/D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts uses it with the uniform-reference inner products of path likelihoods as actual readouts. The definition is an operand for those source-bound registrations, not a theorem or a registration proof.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates.profilePairStepSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates.subcoordinateRecordSignature`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/DependentFamily](DependentFamily.md)
