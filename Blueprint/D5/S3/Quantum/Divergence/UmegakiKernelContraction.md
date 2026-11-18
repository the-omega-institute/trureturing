# Endpoint contraction on the partial-trace kernel

## Abstract

A uniform endpoint estimate implies the arithmetic inverse-form estimate at every parameter.

**Definition 1.1 (The uniform left-endpoint premise).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.EndpointBound`

*Formalization.* `D5/S3/Quantum/Divergence/UmegakiKernelContraction.EndpointBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a canonical finite channel N and coefficient c, quantify over every finite reference and every pair Z,V of complex joint matrices with Z positive definite and ordinary partial trace of V zero. The amplified left-endpoint inverse form is at most c times the input form. The inverse at zero pairs V with Z inverse V.

**Theorem 1.2 (Arithmetic inverse contraction on the kernel).**

Lean statement: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.kernel_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UmegakiKernelContraction.kernel_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a canonical finite channel between nonempty carriers with N(I) positive definite. Let 0 ≤ c ≤ 1 and assume EndpointBound(N,c). For every finite reference, correlated positive definite Z, complex V with zero ordinary partial trace, and u in [0,1], q(amp(N,Z),amp(N,V),u) ≤ c q(Z,V,u). The reference may be empty.

For c < 1, take the endpoint reference center X = (PZ) inverse P(Z PhiR(Y)). The direction Z times (PhiR(Y) minus X tensor I) has zero partial trace. The endpoint inequality and weighted Cauchy–Schwarz bound the centered energy by k times the channel defect, where k = c/(1-c). This gives a universal trace test for the common-state scalarizer.

The scalarizer supplies one state and both residual Gram bounds. With p the input inverse form, q the output inverse form, f the uncentered input energy and d = q-f, the two pairings bound q squared by f p and k d p. For q > 0 their combination yields (1+k)q ≤ k p. The proof handles q = 0 before cancellation, includes c = 0, and at c = 1 uses the uncentered bound and d ≥ 0.

This estimate is used on the actual joint-minus-marginal residual in the faithful density-state theorem. The premise still requires a uniform endpoint bound for all references and complex kernel directions. The coefficient equality for all supported pairs and all channels remains open.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.EndpointBound`
- Truth anchor: `D5/S3/Quantum/Divergence/UmegakiKernelContraction.kernel_contraction`
- Dependency: [D5/S3/Quantum/Divergence/UmegakiReferenceTransport](UmegakiReferenceTransport.md)
