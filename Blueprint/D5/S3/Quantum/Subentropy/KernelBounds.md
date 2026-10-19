# Classical kernel bounds

## Abstract

The classical subentropy kernel has a sharp vertex-dependent integrable bound.

**Theorem 1.1 (A uniform bound at every probability vector).**

Lean statement: `D5/S3/Quantum/Subentropy/KernelBounds.classical_kernel_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/KernelBounds.classical_kernel_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

Let p be any nonnegative finite real vector whose entries sum to one. For every chosen coordinate x and every t>0, its diagonal kernel satisfies 0<=K(diag p,t)<=(1−p_x)/(1+t)^2. Zero probabilities are allowed.

The lower bound uses the product inequality product(1+p_i/t)>=1+1/t. For the upper bound, log u<=u−1 and exp v>=1+v imply product(a_i/b_i)>=1−sum((b_i−a_i)/a_i) for strictly positive vectors a,b. Apply this at a_i=t+delta_ix and b_i=t+p_i; the sum on the right is (1−p_x)/(t(1+t)), and the vertex product is t/(1+t).

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/KernelBounds.classical_kernel_bounds`
- Dependency: [D5/S3/Quantum/Subentropy/Basic](Basic.md)
