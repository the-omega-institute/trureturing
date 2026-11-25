# Fibonacci qutrit spectral transport

## Abstract

A small null-reference loss forces strict rank-two improvement in the Fibonacci qutrit.

**Theorem 1.1 (Strict rank-two improvement).**

Lean statement: `D5/S3/Quantum/Divergence/FibonacciQutritSpectralTransport.strict_spectral_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FibonacciQutritSpectralTransport.strict_spectral_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The mathlib community (2026). *Schur complements of finite matrices*. URL: <https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean#L369-L373>.

*Commentary.*

Take a positive definite qutrit reference C and a trace-one comparison A with 4C/3 ≤ A ≤ 7C/3. Let ρ be a trace-one positive semidefinite null state. Assume c = Re Tr C ≥ 11/19, e ≥ c/3 and Re Tr A[log(C + eρ) − log C] ≤ 1/114.

A floor C ≥ I/500 would force a loss greater than (4/3)(1/500) log 64 ≥ 4/375. Hence the smallest eigenvalue λ lies in (0, 1/500). Conjugate by a unitary eigenbasis and move a λ-coordinate to the ray. Functional calculus and cyclicity of trace preserve the original divergence in these coordinates.

Let E be this coordinate change, Cₚ the retained principal block of EC, and τ = Cₚ/Tr Cₚ. Compress a block matrix by adding its ray mass times τ to its retained principal block. The compressed A and positive reference C are positive semidefinite, retain their respective traces, and have rank at most two. Adding e times the freed ray projection to the compressed C gives a positive definite reference and a strictly larger Umegaki divergence than the original pair.

The same real-linear compression sends each positive source preparation to a trace-one positive semidefinite matrix supported on the retained qubit. It distributes over each finite weighted sum with its original weights. The null preparation becomes the trace-one projection onto the freed ray.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/FibonacciQutritSpectralTransport.strict_spectral_transport`
- Dependency: [D5/S3/Quantum/Divergence/FibonacciQutritBlockDomination](FibonacciQutritBlockDomination.md)
