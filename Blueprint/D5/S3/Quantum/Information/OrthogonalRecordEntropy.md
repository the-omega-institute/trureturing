# Orthogonal Records and Pointer Information

## Abstract

Orthogonal fragment records retain the entire classical entropy of a pointer distribution, conditional on the supplied record structure.

Let p be any finite probability distribution and rho_i any fragment density states. The physical hypothesis is explicit: rho_i rho_j = 0 for i != j. No observer assumption is claimed to imply this record structure. Zero weights and singular density states are allowed.

**Theorem 1.1 (Entropy of an orthogonal mixture).**

$$\operatorname{Orthogonal}\left(\rho\right) \Rightarrow \operatorname{S}\left(\operatorname{mixture}\left(p, \rho\right)\right) = \operatorname{H}\left(p\right) + \operatorname{WeightedEntropy}\left(p, \rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/OrthogonalRecordEntropy.orthogonal_mixture_entropy` (`✓ std3`). ∎

*Citation.* Thao P. Le and Alexandra Olaya-Castro (2019). *Strong Quantum Darwinism and Strong Independence is equivalent to Spectrum Broadcast Structure*. URL: <https://arxiv.org/html/1803.08936>.

*Commentary.*

For the mixture sum_i p_i rho_i, its von Neumann entropy equals H(p) plus sum_i p_i S(rho_i). WeightedEntropy denotes that latter finite sum. Orthogonal positive operators are the positive and negative parts of their difference. Functional calculus and the scalar product identity for negative x log x give the decomposition.

**Theorem 1.2 (The fragment carries all pointer information).**

$$\operatorname{Orthogonal}\left(\rho\right) \Rightarrow \operatorname{quantumMutualInformation}\left(\operatorname{recordState}\left(p, \rho\right)\right) = \operatorname{H}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/OrthogonalRecordEntropy.orthogonal_record_trace_gives_sbs_consensus` (`✓ std3`). ∎

*Citation.* Thao P. Le and Alexandra Olaya-Castro (2019). *Strong Quantum Darwinism and Strong Independence is equivalent to Spectrum Broadcast Structure*. URL: <https://arxiv.org/html/1803.08936>.

*Commentary.*

The joint state is sum_i p_i |i><i| tensor rho_i. Its system marginal is the diagonal pointer distribution and its fragment marginal is the mixture. Both marginals are computed by partial trace. Applying the entropy decomposition to the joint state and fragment gives I = H(p). This equality is the information content of the conditional result; measurement instruments and multi-observer protocols are outside scope.

## References

- Truth anchor: `D5/S3/Quantum/Information/OrthogonalRecordEntropy.orthogonal_mixture_entropy`
- Truth anchor: `D5/S3/Quantum/Information/OrthogonalRecordEntropy.orthogonal_record_trace_gives_sbs_consensus`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../Entropy/MaxEntropy.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
