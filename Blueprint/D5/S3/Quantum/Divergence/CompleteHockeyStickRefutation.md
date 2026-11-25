# Complete hockey-stick contraction with a quantum reference

## Abstract

A binary measure-and-prepare channel refutes nonincreasing complete hockey-stick contraction and orthogonal reduction.

**Definition 1.1 (Complete hockey-stick coefficient).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation.completeCoefficient`

*Formalization.* `D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation.completeCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

Take the supremum of joint output-to-input hockey-stick ratios over all finite reference systems and pairs of density matrices with identical reference marginals and positive denominators. The Boolean parameter optionally requires orthogonal input supports. Include zero for an empty ratio set.

**Theorem 1.2 (An increase at gamma two and a strict orthogonal-input gap).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation.refutes_monotonicity_and_orthogonal_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation.refutes_monotonicity_and_orthogonal_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The channel measures the input in its computational basis and prepares the rays of (1,0) and (4/5,3/5). At gamma one, an equal-reference-marginal difference has opposite diagonal blocks D and minus D. Its output is D tensor the prepared-state contrast. Pinching and trace-norm multiplicativity give the upper bound 3/5 for every finite reference. Orthogonal inputs have denominator one and their output divergence decreases with gamma, so their ratios are bounded by 3/5 for all gamma at least one.

On a two-dimensional reference, the two input difference blocks at gamma two are diag(1,-64)/131 and minus 4/131 times the outer product of (1,-4). The input divergence is 1/131. Testing the output on the normalized ray of (3,0,0,1) gives 9/1310. Thus the unrestricted coefficient is at least 9/10, strictly above both bounds. This supplies explicit negative answers for the complete coefficient in Remark 6 and Section 9.

Lluis Eriksson, Common support and complete contraction with quantum side information, v3, Section 6.4, gives a complete Umegaki ratio above the trace endpoint for a different channel. The Hirche–Tomamichel integral representation then implies the qualitative failures at some parameter above one. The rational construction here fixes the parameter at two.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation.completeCoefficient`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation.refutes_monotonicity_and_orthogonal_reduction`
- Dependency: [D5/S3/Quantum/Divergence/FaithfulConditionalGap](FaithfulConditionalGap.md)
- Dependency: [D5/S3/Quantum/Foundation/TraceNormTensorProduct](../Foundation/TraceNormTensorProduct.md)
