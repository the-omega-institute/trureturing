# The kernel and trace criteria are not equivalent

## Abstract

The kernel criterion for optimality of entanglement witnesses does not imply the trace criterion.

The dimensions m and n are arbitrary natural numbers. Fin m and Fin n index the two factors, and all matrices and vectors have complex entries. A product vector has coordinate x(p.1)y(p.2). star denotes complex conjugation, dotProduct is the bilinear coordinate sum, mulVec is matrix action, and kronecker is the Kronecker product of matrices. Complex nonnegativity requires a nonnegative real part and zero imaginary part. toLp places a coordinate vector in EuclideanSpace with its standard inner product. The Lean names trTwo and trOne have notation tr₂ and tr₁, respectively. ofReal and natCastComplex display the scalar embeddings used in Lean.

**Definition 1.1 (Block positivity).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall W \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; (\operatorname{blockPositive}\left(W\right)) \Leftrightarrow (\forall x \in \operatorname{Fin}\left(m\right) \to Complex,\; \forall y \in \operatorname{Fin}\left(n\right) \to Complex,\; 0 \le \operatorname{dotProduct}\left(\operatorname{star}\left((\lambda p:\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), x\left(\operatorname{fst}\left(p\right)\right) \cdot y\left(\operatorname{snd}\left(p\right)\right))\right), \operatorname{mulVec}\left(W, (\lambda p:\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), x\left(\operatorname{fst}\left(p\right)\right) \cdot y\left(\operatorname{snd}\left(p\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.blockPositive` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

Section II B requires a nonnegative complex expectation on every product vector, without normalization assumptions on either factor.

**Definition 1.2 (Entanglement witnesses).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall W \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; (\operatorname{IsWitness}\left(W\right)) \Leftrightarrow ((\operatorname{blockPositive}\left(W\right)) \land (\exists sigma \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; (\operatorname{PosSemidef}\left(sigma\right)) \land (\operatorname{trace}\left(W \cdot sigma\right) < 0)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.IsWitness` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

A block-positive matrix is a witness when some positive semidefinite matrix sigma satisfies the strict negative trace inequality tr(W sigma) < 0.

**Definition 1.3 (Trace over the second factor).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall W \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; \forall i \in \operatorname{Fin}\left(m\right),\; \forall k \in \operatorname{Fin}\left(m\right),\; \operatorname{trTwo}\left(W\right)\left(i, k\right) = \sum_{{j:\operatorname{Fin}\left(n\right)}}(W\left(\operatorname{pair}\left(i, j\right), \operatorname{pair}\left(k, j\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.trTwo` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

trTwo is the existing partialTraceRight: sum over the repeated second index while retaining the first factor.

**Definition 1.4 (Trace over the first factor).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall W \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \forall l \in \operatorname{Fin}\left(n\right),\; \operatorname{trOne}\left(W\right)\left(j, l\right) = \sum_{{i:\operatorname{Fin}\left(m\right)}}(W\left(\operatorname{pair}\left(i, j\right), \operatorname{pair}\left(i, l\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.trOne` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

trOne is the existing partialTraceLeft: sum over the repeated first index while retaining the second factor.

**Definition 1.5 (Schmidt rank).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall v \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right) \to Complex,\; \operatorname{schmidtRank}\left(v\right) = \operatorname{rank}\left(\operatorname{of}\left((\lambda i:\operatorname{Fin}\left(m\right), \lambda j:\operatorname{Fin}\left(n\right), v\left(\operatorname{pair}\left(i, j\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.schmidtRank` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

Remark 3(i) defines Schmidt rank as the rank of the vector's coefficient matrix.

**Definition 1.6 (The kernel criterion).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall W \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; (\operatorname{kernelCriterion}\left(W\right)) \Leftrightarrow (((m \le n) \land (\exists v \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right) \to Complex,\; (\operatorname{mulVec}\left((W + \operatorname{kronecker}\left(\operatorname{trTwo}\left(W\right), 1\right)), v\right) = 0) \land (\operatorname{schmidtRank}\left(v\right) = m))) \lor ((n \le m) \land (\exists v \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right) \to Complex,\; (\operatorname{mulVec}\left((W + \operatorname{kronecker}\left(1, \operatorname{trOne}\left(W\right)\right)), v\right) = 0) \land (\operatorname{schmidtRank}\left(v\right) = n))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.kernelCriterion` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

Theorem 2 uses a full Schmidt-rank vector in one of the two partial-trace-shifted kernels. Both alternatives, with their dimension inequalities, are retained.

**Definition 1.7 (Maximally entangled states).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall Omega \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right) \to Complex,\; (\operatorname{maximallyEntangled}\left(Omega\right)) \Leftrightarrow (\exists u \in \operatorname{Fin}\left(\operatorname{min}\left(m, n\right)\right) \to \left(\operatorname{Fin}\left(m\right) \to Complex\right),\; \exists w \in \operatorname{Fin}\left(\operatorname{min}\left(m, n\right)\right) \to \left(\operatorname{Fin}\left(n\right) \to Complex\right),\; (\operatorname{Orthonormal}\left(Complex, (\lambda j:\operatorname{Fin}\left(\operatorname{min}\left(m, n\right)\right), \operatorname{toLp}\left(2, u\left(j\right)\right))\right)) \land ((\operatorname{Orthonormal}\left(Complex, (\lambda j:\operatorname{Fin}\left(\operatorname{min}\left(m, n\right)\right), \operatorname{toLp}\left(2, w\left(j\right)\right))\right)) \land (Omega = \sum_{{j:\operatorname{Fin}\left(\operatorname{min}\left(m, n\right)\right)}}(\operatorname{smul}\left(\operatorname{ofReal}\left(\operatorname{natCastReal}\left(\operatorname{min}\left(m, n\right)\right)^{-\frac{1}{2}}\right), (\lambda p:\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), u\left(j\right)\left(\operatorname{fst}\left(p\right)\right) \cdot w\left(j\right)\left(\operatorname{snd}\left(p\right)\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.maximallyEntangled` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

Corollary 2 uses min(m,n) orthonormal vectors in each factor with every Schmidt coefficient equal to min(m,n) raised to negative one half. The orthonormality predicates use the standard complex Euclidean inner product.

**Definition 1.8 (The trace criterion).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall W \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; (\operatorname{traceCriterion}\left(W\right)) \Leftrightarrow (\exists Omega \in \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right) \to Complex,\; (\operatorname{maximallyEntangled}\left(Omega\right)) \land (\operatorname{dotProduct}\left(\operatorname{star}\left(Omega\right), \operatorname{mulVec}\left(W, Omega\right)\right) = -\frac{\operatorname{trace}\left(W\right)}{\operatorname{natCastComplex}\left(\operatorname{min}\left(m, n\right)\right)}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.traceCriterion` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

The trace criterion is equality in equation (11) for at least one maximally entangled state. The equality is an equality of complex numbers.

**Definition 1.9 (The equivalence question).**

$$(claim) \Leftrightarrow (\forall m \in Nat,\; \forall n \in Nat,\; \forall W \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right)\right), Complex\right),\; (\operatorname{IsWitness}\left(W\right)) \Rightarrow ((\operatorname{kernelCriterion}\left(W\right)) \Leftrightarrow (\operatorname{traceCriterion}\left(W\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.claim` (`✓ std3`).

*Citation.* Frederik vom Ende and Simon Cichy (2025). *Simple Sufficient Criteria for Optimality of Entanglement Witnesses*. URL: <https://arxiv.org/abs/2505.15615v2>.

*Commentary.*

Section IV asks whether the trace-based criterion of Corollary 2 is equivalent to the kernel criterion of Theorem 2. The statement quantifies over all finite dimensions and every witness.

**Theorem 1.10 (The equivalence is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/vom-ende-cichy-2025-kernel-trace-criteria-refutation` (refuted) by `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vom-ende-cichy-2025-kernel-trace-criteria-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

In the ordered basis (00,01,10,11), take W with rows (0,0,0,-2), (0,1,0,0), (0,0,4,0), (-2,0,0,0). Its product expectation is the squared modulus of conjugate(x(0))y(1)-2conjugate(x(1))y(0), so it is block positive. The Bell vector (1,0,0,1)/sqrt(2) gives a positive semidefinite outer product with trace pairing -2. The second partial trace is diag(1,4); the shifted matrix annihilates (2,0,0,1), whose coefficient matrix diag(2,1) has rank two. Every maximally entangled state has squared norm one. For any z, the quadratic form of W+2I is 2|z(00)-z(11)| squared plus 3|z(01)| squared plus 6|z(10)| squared. Consequently every such state's expectation is at least -2, whereas the trace criterion requires -5/2. Thus this witness satisfies the kernel criterion and fails the trace criterion. This conclusion does not alter either criterion's sufficient implication to optimality.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.IsWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.blockPositive`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.kernelCriterion`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.maximallyEntangled`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.schmidtRank`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.trOne`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.trTwo`
- Truth anchor: `D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.traceCriterion`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
