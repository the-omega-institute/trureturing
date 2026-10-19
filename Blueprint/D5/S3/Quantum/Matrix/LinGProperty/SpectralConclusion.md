# The normalized geometric-mean comparison

## Abstract

The normalized geometric-mean comparison.

**Theorem 1.1 (The normalized geometric-mean comparison).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/SpectralConclusion.normalized_conclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/SpectralConclusion.normalized_conclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

Assume both positive diagonal blocks have trace one and the trace-corrected arithmetic singular-value estimate. Write t=|trace X|. The difference-square estimate bounds the geometric mean below by H-(1-t squared)/(4c) I, where H=cI+(A+B)/2. The scalar perturbation estimate bounds the augmented cross block by the selected eigenvalue of H minus (c-1/2)(1-t). For c at least one and t between zero and one, the latter deficit is at least the former correction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/SpectralConclusion.normalized_conclusion`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound](GeometricMeanBound.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/Normalization](Normalization.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation](ScalarPerturbation.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/TraceDistanceBound](TraceDistanceBound.md)
