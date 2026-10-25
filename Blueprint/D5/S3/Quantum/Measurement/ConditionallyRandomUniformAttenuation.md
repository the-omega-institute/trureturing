# Conditional randomness and uniform attenuation

## Abstract

Conditional randomness implies uniform attenuation for all finite quantum observables.

**Definition 1.1 (The conditioned matrix family).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(B: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(y: \operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.conditioned}\left(A, B, y\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\lambda \left(x: \operatorname{Fin}\left(m\right)\right) \mapsto \left(\operatorname{CFC.sqrt}\left(A\left(x\right)\right)\right), B\left(y\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.conditioned` (`✓ std3`).

*Citation.* Stan Gudder (2021). *Mutually Unbiased Quantum Observables*. DOI: [10.48550/arXiv.2110.03099](https://doi.org/10.48550/arXiv.2110.03099). URL: <https://arxiv.org/abs/2110.03099v1>.

*Commentary.*

For finite complex matrix families A and B, the conditioned matrix at outcome y is the unread operation on B y with operators CFC.sqrt (A x). This operation sums K x * B y * K x over x. For positive effects the square roots are Hermitian, so this is the sum of the sequential products A x ∘ B y. Gudder defines the sequential product in the arXiv v1 TeX at line 97 and the conditioned observable at lines 117–120.

**Definition 1.2 (Uniform attenuation in both orders).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(B: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.UniformAttenuation}\left(A, B\right)\right) \Leftrightarrow \left(\forall \left(x: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(y: \operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality.luders}\left(A\left(x\right), B\left(y\right)\right) = \left(\frac{\left(1: \mathbb{C}\right)}{\left(\operatorname{Nat.cast}\left(n\right): \mathbb{C}\right)}\right) \cdot \left(A\left(x\right)\right)\right) \land \left(\operatorname{D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality.luders}\left(B\left(y\right), A\left(x\right)\right) = \left(\frac{\left(1: \mathbb{C}\right)}{\left(\operatorname{Nat.cast}\left(m\right): \mathbb{C}\right)}\right) \cdot \left(B\left(y\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.UniformAttenuation` (`✓ std3`).

*Citation.* Stan Gudder (2021). *Mutually Unbiased Quantum Observables*. DOI: [10.48550/arXiv.2110.03099](https://doi.org/10.48550/arXiv.2110.03099). URL: <https://arxiv.org/abs/2110.03099v1>.

*Commentary.*

For every outcome x of A and y of B, measuring B y after A x gives A x divided by n, and measuring A x after B y gives B y divided by m. The operation luders E F is CFC.sqrt E * F * CFC.sqrt E. This is Condition (1) in Gudder's arXiv v1 TeX, lines 174–182. The natural numbers n and m are explicitly cast to complex scalars before division. The predicate itself applies to arbitrary matrix families; positivity and normalization are separate conditions.

**Definition 1.3 (Conditional randomness in both orders).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(B: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.ConditionallyRandom}\left(A, B\right)\right) \Leftrightarrow \left(\left(\forall \left(y: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.conditioned}\left(A, B, y\right) = \left(\frac{\left(1: \mathbb{C}\right)}{\left(\operatorname{Nat.cast}\left(n\right): \mathbb{C}\right)}\right) \cdot \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right) \land \left(\forall \left(x: \operatorname{Fin}\left(m\right)\right), \left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.conditioned}\left(B, A, x\right) = \left(\frac{\left(1: \mathbb{C}\right)}{\left(\operatorname{Nat.cast}\left(m\right): \mathbb{C}\right)}\right) \cdot \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.ConditionallyRandom` (`✓ std3`).

*Citation.* Stan Gudder (2021). *Mutually Unbiased Quantum Observables*. DOI: [10.48550/arXiv.2110.03099](https://doi.org/10.48550/arXiv.2110.03099). URL: <https://arxiv.org/abs/2110.03099v1>.

*Commentary.*

Each conditioned outcome of B given A is the identity matrix divided by n, and each conditioned outcome of A given B is the identity matrix divided by m. For observables, this means that both conditioned observables have uniform outcome probabilities in every state. This is Condition (2) in Gudder's arXiv v1 TeX, lines 174–182. The displayed predicate places no positivity or normalization condition on A or B.

**Definition 1.4 (The converse for arbitrary finite observables).**

$$\left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(B: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\left(0: \mathbb{N}\right) < m\right) \to \left(\left(\left(0: \mathbb{N}\right) < n\right) \to \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(B\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.ConditionallyRandom}\left(A, B\right)\right) \to \left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.UniformAttenuation}\left(A, B\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Stan Gudder (2021). *Mutually Unbiased Quantum Observables*. DOI: [10.48550/arXiv.2110.03099](https://doi.org/10.48550/arXiv.2110.03099). URL: <https://arxiv.org/abs/2110.03099v1>.

*Commentary.*

For every natural dimension d and positive outcome counts m and n, two positive operator valued measures that are conditionally random uniformly attenuate each other. Here IsPOVM means that every matrix in the family is positive semidefinite and the family sums to the identity. No projection or sharpness condition is imposed, and dimension zero is included. This is the converse of Theorem 2.1(i), stated in Gudder's arXiv v1 TeX at lines 184–186; the question at line 223 asks whether this converse holds. The separate question concerning the converse of part (ii) is not asserted here.

**Theorem 1.5 (Conditional randomness forces uniform attenuation).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(A: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\forall \left(B: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\left(0: \mathbb{N}\right) < m\right) \to \left(\left(\left(0: \mathbb{N}\right) < n\right) \to \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(A\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(B\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.ConditionallyRandom}\left(A, B\right)\right) \to \left(\operatorname{D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation.UniformAttenuation}\left(A, B\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gudder-2021-conditionally-random-uniform-attenuation` (proved) by `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gudder-2021-conditionally-random-uniform-attenuation","declaration_gid":"D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stan Gudder (2021). *Mutually Unbiased Quantum Observables*. DOI: [10.48550/arXiv.2110.03099](https://doi.org/10.48550/arXiv.2110.03099). URL: <https://arxiv.org/abs/2110.03099v1>.

*Commentary.*

First let K be positive semidefinite and X Hermitian. Set R = CFC.sqrt K. Then R is Hermitian, R * R = K, and R * X * R is Hermitian. Cyclicity of the trace, followed by substitution of R * R for K, gives trace (X * (K * X * K)) = trace ((R * X * R).conjTranspose * (R * X * R)). The right side is nonnegative because it is the trace of a matrix of the form Y.conjTranspose * Y.

Next let K be a finite family of positive semidefinite matrices and suppose that the sum of K x * X * K x over x is zero. Multiply this equality on the left by X and take the trace. Linearity gives a sum of the preceding nonnegative traces equal to zero, so every trace is zero. For each x, trace (Y.conjTranspose * Y) = 0 implies Y = 0, with Y = CFC.sqrt (K x) * X * CFC.sqrt (K x). Multiplying this zero matrix on both sides by CFC.sqrt (K x) gives K x * X * K x = 0.

Now let A be a positive operator valued measure, B a Hermitian matrix, and c a self-adjoint complex scalar. Suppose the sum of luders (A x) B over x is c times the identity. The identity CFC.sqrt (A x) * CFC.sqrt (A x) = A x shows that CFC.sqrt (A x) * (B − c • 1) * CFC.sqrt (A x) = luders (A x) B − c • A x. Summing and using the normalization of A makes this sum zero. The matrix B − c • 1 is Hermitian, and every CFC.sqrt (A x) is positive semidefinite. Apply the preceding conclusion with K x = CFC.sqrt (A x) and X = B − c • 1. Every centered summand vanishes, hence luders (A x) B = c • A x for every x.

Finally fix d, m, n, A and B satisfying the displayed hypotheses. For each y, the first conditional-randomness equality supplies the required sum for the observable A, the Hermitian matrix B y and the self-adjoint scalar c = 1 / (n : ℂ). It follows that luders (A x) (B y) = (1 / (n : ℂ)) • A x for every x. Exchange A and B and use the second conditional-randomness equality with c = 1 / (m : ℂ) to obtain luders (B y) (A x) = (1 / (m : ℂ)) • B y. These are the two required identities for every x and y.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.ConditionallyRandom`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.UniformAttenuation`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.conditioned`
- Truth anchor: `D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.result`
- Dependency: [D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality](../Measurements/CalibratedJointMeasurabilityOptimality.md)
