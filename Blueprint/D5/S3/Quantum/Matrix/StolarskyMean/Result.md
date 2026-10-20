# Integrating positive mixed curvature

## Abstract

Positive profile curvature implies conditional negativity and the class A property for Stolarsky mean matrices.

**Definition 1.1 (Exponential homogeneous reconstruction).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Result.logKernel`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Result.logKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real profile g determines the kernel exp((x+y)/2) g((y-x)/2). For the Stolarsky profile this is the mean of exp(x) and exp(y). These coordinates keep all scalar derivatives on the whole real line.

**Theorem 1.2 (Hilbert features integrate to negative type).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_of_mixed_feature`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_of_mixed_feature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K have a first partial derivative Kx and let v be a continuous path in a real Hilbert space. If the second partial derivative in the other coordinate is minus the inner product of the two feature vectors, then every finite matrix of K is conditionally negative. Integrating v from zero defines V. Two applications of the zero derivative criterion give K(x,y)-K(x,0)-K(0,y)+K(0,0)=-inner(V(x),V(y)). For coefficients summing to zero, the quadratic form is minus the squared norm of the weighted sum of V.

**Theorem 1.3 (Positive profile curvature gives conditional negativity).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_logKernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_logKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a twice continuously differentiable real profile g, assume that g''-g is positive definite in the finite translation matrix sense. The corresponding scalar kernel generates a reproducing kernel Hilbert space by the Mathlib construction. Joint continuity gives a continuous feature path. Multiplication by exp(x/2)/2 and dilation by one half produce a feature for the negative mixed derivative of the exponential homogeneous reconstruction. The Hilbert integration theorem then proves conditional negativity on every finite configuration.

**Theorem 1.4 (Conditional negativity of Stolarsky mean matrices).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_stolarsky`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_stolarsky` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real parameter at least two and every finite positive family, the Stolarsky mean matrix is conditionally negative. KernelFactor supplies global smoothness of its exponential profile and positive definiteness of its second derivative defect. The exponential reconstruction theorem applies at the logarithms of the positive inputs. Repeated inputs and the empty family are allowed.

**Theorem 1.5 (Exactly one positive eigenvalue).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Result.inClassA_stolarsky`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Result.inClassA_stolarsky` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real parameter at least two and every nonempty finite positive family, the Stolarsky mean matrix has positive entries and exactly one strictly positive eigenvalue, counted with multiplicity. Symmetry and positivity come from the scalar mean. Conditional negativity limits the positive spectral subspace to dimension at most one, while a positive diagonal entry supplies a positive direction.

**Theorem 1.6 (The Stolarsky matrix conjecture).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/bhatia-jain-2016-stolarsky-mean-matrices-class-a` (proved) by `D5/S3/Quantum/Matrix/StolarskyMean/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhatia-jain-2016-stolarsky-mean-matrices-class-a","declaration_gid":"D5/S3/Quantum/Matrix/StolarskyMean/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Bhatia and T. Jain (2016). *Mean matrices and conditional negativity*. DOI: [10.13001/1081-3810.3082](https://doi.org/10.13001/1081-3810.3082). URL: <https://journals.uwyo.edu/index.php/ela/article/view/1495>.

*Commentary.*

Every real parameter at least two gives a class A Stolarsky matrix for every nonempty finite positive family. Every parameter from zero inclusive to two exclusive admits a positive three-point family whose mean matrix has at least two positive eigenvalues. The first conclusion follows from positive profile curvature, Hilbert feature integration and the spectral bound. The second uses the ThreePoint theorem. The definitions and the conjecture are those of Bhatia and Jain; the proofs are formal derivations in this repository.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_logKernel`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_of_mixed_feature`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Result.conditionallyNegative_stolarsky`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Result.inClassA_stolarsky`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Result.logKernel`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Result.result`
- Dependency: [D5/S3/Quantum/Matrix/StolarskyMean/KernelFactor](KernelFactor.md)
- Dependency: [D5/S3/Quantum/Matrix/StolarskyMean/ThreePoint](ThreePoint.md)
