# Pure Output Trace Distance

## Abstract

An overlap estimate for the trace distance between pure unitary outputs.

**Lemma 1.1 (Trace norm bounded by the orthogonal residual).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PureDistance.traceNorm_pure_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PureDistance.traceNorm_pure_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

For unit Euclidean vectors x and y, the trace norm of the difference of their outer projectors is at most twice the square root of one minus the squared modulus of their inner product. The proof splits the projector difference into two outer products and applies the rank-one trace-norm estimate.

**Lemma 1.2 (Pure joint inputs to two unitary channels).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/PureDistance.pure_referenceError_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/PureDistance.pure_referenceError_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nathaniel Johnston, David W. Kribs and Vern I. Paulsen (2009). *Computing stabilized norms for quantum operations*. DOI: [10.26421/QIC9.1-2-2](https://doi.org/10.26421/QIC9.1-2-2). URL: <https://arxiv.org/abs/0711.3636v1>.

*Commentary.*

Represent a pure state on an arbitrary finite reference and the global input by a unit vector. The unhalved reference error between its two conjugation outputs is bounded by the same overlap expression for the vectors produced by the reference-amplified unitaries.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PureDistance.pure_referenceError_le`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/PureDistance.traceNorm_pure_sub_le`
- Dependency: [D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels](ReconstructionChannels.md)
