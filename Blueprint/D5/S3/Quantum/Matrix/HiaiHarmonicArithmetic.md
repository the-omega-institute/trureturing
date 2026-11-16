# Harmonic arithmetic mean parameter necessity

## Abstract

Harmonic arithmetic mean parameter necessity

**Definition 1.1 (Quasi-arithmetic matrix mean).**

Lean statement: `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.powerMean`

*Formalization.* `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.powerMean` (`✓ std3`).

*Citation.* Fumio Hiai (2025). *Various inequalities between quasi-arithmetic mean and quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2508.20309>.

*Commentary.*

For a weight alpha strictly between zero and one and a nonzero real parameter t, this is the one over t power of the weighted sum of the t powers of A and B. Powers use continuous functional calculus. The theorem uses positive definite complex matrices, where this agrees with the spectral definition in Section 2.1.

**Definition 1.2 (Quasi-harmonic matrix mean).**

Lean statement: `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.harmonicMean`

*Formalization.* `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.harmonicMean` (`✓ std3`).

*Citation.* Fumio Hiai (2025). *Various inequalities between quasi-arithmetic mean and quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2508.20309>.

*Commentary.*

Raise A and B to p, take the inverse of the weighted sum of their inverses, and then take the one over p power. On positive definite matrices this equals the quasi-arithmetic mean with parameter minus p; the identity is proved in the module.

**Theorem 1.3 (Both parameters must be at least one).**

Lean statement: `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.result` (`✓ std3`). ∎

*Resolves.* `Problems/hiai-2025-harmonic-arithmetic-mean-necessity` (proved) by `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hiai-2025-harmonic-arithmetic-mean-necessity","declaration_gid":"D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2025). *Various inequalities between quasi-arithmetic mean and quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2508.20309>.

*Commentary.*

The Lean conclusion concerns alpha strictly between zero and one, positive parameters p and q, and positive definite two by two complex matrices. If the quasi-harmonic mean with parameter p is below the quasi-arithmetic mean with parameter q in the Loewner order for every such pair, then p and q are both at least one. This answers Section 5 (4) of arXiv:2508.20309v2: together with the source sufficiency and the paper direct sum extension, it gives the complete characterization for alpha strictly between zero and one on positive semidefinite matrices in every dimension at least two. The real symmetric test family is embedded in complex matrices: A has eigenvalues one and x, while B has eigenvalues one and x squared and is rotated by an angle with squared sine z. Two-point functional calculus computes its power means. A derivative with respect to z at zero gives the determinant coefficient. For p below one the first term in the simplified coefficient tends to zero, while the magnitude of its negative term tends to the square of one minus alpha; the coefficient therefore tends to the negative square of one minus alpha. Positive semidefiniteness would force that coefficient to be nonnegative. Inverting both inputs and reversing the inverse order gives the necessity for q. The source sufficiency for parameters at least one, including its limiting definition of the harmonic mean on singular inputs, is not formalized here. The positive definite counterexamples already belong to the positive semidefinite domain; their extension by a common identity block is a paper consequence, not an additional Lean conclusion. At alpha zero or one both means equal the same input for all positive parameters, and in dimension one the scalar comparison holds for all positive parameters; these statements are also not formalized here.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.harmonicMean`
- Truth anchor: `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.powerMean`
- Truth anchor: `D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic.result`
- Dependency: [D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus](TwoPointFunctionalCalculus.md)
