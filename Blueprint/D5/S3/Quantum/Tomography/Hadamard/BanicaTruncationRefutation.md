# Fourier truncation and phase deformations

## Abstract

Fourier truncation, analytic phase curves and the real-density isolation assertion.

**Definition 1.1 (Partial Fourier matrices).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.partialFourier`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.partialFourier` (`✓ std3`).

*Citation.* T. Banica; D. Özteke; L. Pittau (2018). *Isolated partial Hadamard matrices, and related topics*. DOI: [10.1142/S1230161218500099](https://doi.org/10.1142/S1230161218500099). URL: <https://arxiv.org/abs/1706.00986v2>.

*Commentary.*

For positive p, the row set S is a finite subset of Z/pZ and every column is retained. The (s,j) entry is exp(2 pi i val(s) val(j)/p).

**Definition 1.2 (Partial Hadamard matrices).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsPartialHadamard`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsPartialHadamard` (`✓ std3`).

*Citation.* T. Banica; D. Özteke; L. Pittau (2018). *Isolated partial Hadamard matrices, and related topics*. DOI: [10.1142/S1230161218500099](https://doi.org/10.1142/S1230161218500099). URL: <https://arxiv.org/abs/1706.00986v2>.

*Commentary.*

In source Definition 1.1, every entry has complex norm one, and the Hermitian inner product of any two distinct rows is zero.

**Definition 1.3 (Analytic deformations).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsDeformation`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsDeformation` (`✓ std3`).

*Citation.* T. Banica; D. Özteke; L. Pittau (2018). *Isolated partial Hadamard matrices, and related topics*. DOI: [10.1142/S1230161218500099](https://doi.org/10.1142/S1230161218500099). URL: <https://arxiv.org/abs/1706.00986v2>.

*Commentary.*

This is the analytic specialization of source Definition 1.3: a globally real analytic matrix curve through H whose values near zero are partial Hadamard matrices. Use the local coordinate q = exp(i t), with q near 1 on the unit circle and real t near 0. On the principal branch, q^alpha = exp(i alpha t) for real alpha. Real analyticity implies continuous differentiability of every finite order.

**Definition 1.4 (Row and column phase deformations).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsTrivialDeformation`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsTrivialDeformation` (`✓ std3`).

*Citation.* T. Banica; D. Özteke; L. Pittau (2018). *Isolated partial Hadamard matrices, and related topics*. DOI: [10.1142/S1230161218500099](https://doi.org/10.1142/S1230161218500099). URL: <https://arxiv.org/abs/1706.00986v2>.

*Commentary.*

This generalizes the trivial deformations of source Definition 1.3: near zero, each entry is H(s,j) exp(i (a(s,t)+b(j,t))), with no regularity required of the real phase functions. In the local coordinate q = exp(i t), with q near 1 and t near 0, the principal branch gives q^alpha = exp(i alpha t). Thus the source's f_ij(q)=H_ij q^{alpha_i+beta_j} is included by taking a_i(t)=t alpha_i and b_j(t)=t beta_j. Source isolation implies isolation in this encoding, which tests analytic curves against a larger trivial class; hence the encoded negation of the conjecture refutes the source conjecture.

**Definition 1.5 (Isolation).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsolatedPartialHadamard`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsolatedPartialHadamard` (`✓ std3`).

*Citation.* T. Banica; D. Özteke; L. Pittau (2018). *Isolated partial Hadamard matrices, and related topics*. DOI: [10.1142/S1230161218500099](https://doi.org/10.1142/S1230161218500099). URL: <https://arxiv.org/abs/1706.00986v2>.

*Commentary.*

This is the analytic specialization of isolation following source Definition 1.3: every analytic deformation through H must agree near zero with row and column phase multiplication. The enlarged trivial class makes this isolation condition weaker than source isolation.

**Definition 1.6 (The real-density truncation assertion).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.claim`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.claim` (`✓ std3`).

*Citation.* T. Banica; D. Özteke; L. Pittau (2018). *Isolated partial Hadamard matrices, and related topics*. DOI: [10.1142/S1230161218500099](https://doi.org/10.1142/S1230161218500099). URL: <https://arxiv.org/abs/1706.00986v2>.

*Commentary.*

In this analytic specialization of source Conjecture 1.14, there is a positive real epsilon such that, for every prime p and every row set S with cardinality at least (1-epsilon)p, the prescribed partial Fourier matrix is isolated.

**Theorem 1.7 (Fourier orthogonality).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.partial_fourier_isPartialHadamard`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.partial_fourier_isPartialHadamard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prescribed exponential Fourier entries agree with the standard additive character. The character has unit modulus, and its nonzero-frequency sums vanish, proving the partial Hadamard condition.

**Theorem 1.8 (A nontrivial tangent produces a nontrivial curve).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.not_isolated_of_regular_tangent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.not_isolated_of_regular_tangent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the real phase Jacobian is surjective and has a kernel vector outside the additive row-column phase space. An analytic regular-level curve realizes a positive multiple of that vector. For nonempty row and column sets, triviality forces equality of the two cross-products of phase exponentials at each parameter. Differentiating these smooth cross-products at zero makes every tangent cross-difference vanish, putting the tangent inside the row-column space, a contradiction. The arbitrary trivial phase functions are never differentiated.

**Theorem 1.9 (Deleting two rows).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.two_row_truncation_not_isolated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.two_row_truncation_not_isolated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p at least five and every row set of cardinality p-2, the Fourier phase Jacobian is surjective. Its kernel has dimension 3(p-2), exceeding the additive row-column parameter bound 2p-2. A tangent outside that space therefore gives a nontrivial analytic matrix deformation.

**Theorem 1.10 (The density assertion is false).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/banica-ozteke-pittau-2018-truncation-isolation` (refuted) by `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"banica-ozteke-pittau-2018-truncation-isolation","declaration_gid":"D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

For any positive real epsilon, choose a sufficiently large prime p and delete two rows. The remaining density is at least 1-epsilon, while the resulting partial Fourier matrix admits a nontrivial analytic deformation.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsDeformation`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsPartialHadamard`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsTrivialDeformation`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.IsolatedPartialHadamard`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.not_isolated_of_regular_tangent`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.partialFourier`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.partial_fourier_isPartialHadamard`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.result`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation.two_row_truncation_not_isolated`
- Dependency: [D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve](BanicaLevelSetCurve.md)
- Dependency: [D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationJacobian](BanicaTruncationJacobian.md)
