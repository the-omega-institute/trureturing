# A triangle inequality fails for unified-entropy correlations

## Abstract

A two-qubit density matrix violates the unified-entropy correlation triangle inequality at q = 2 and s = -1.

**Definition 1.1 (The spectral power trace).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.genPurity}\left(q, \sigma\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Matrix.SpectralPower.mpow}\left(\sigma, q\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.genPurity` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

The generalized purity is the real part of the trace of the real spectral power of σ. For positive semidefinite σ this is the sum of the qth powers of its eigenvalues, the quantity Tr ρ^q in Unifiedarxiv.tex, lines 187–194. The spectral power uses the continuous functional calculus with the real power function. Its total definition also accepts matrices and indices outside the density-matrix setting.

**Definition 1.2 (Unified entropy).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(s: \mathbb{R}\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.unifiedEntropy}\left(q, s, \sigma\right) = \frac{\left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.genPurity}\left(q, \sigma\right)\right)^{s} - \left(1: \mathbb{R}\right)}{\left(\left(1: \mathbb{R}\right) - q\right) \cdot s}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.unifiedEntropy` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

This is the unified entropy of Unifiedarxiv.tex, lines 187–194. The source assumes a density matrix and q > 0, q ≠ 1 and s ≠ 0. The displayed function is defined for all real q and s and all complex square matrices; real powers and division use their total real definitions. The limits q = 1 and s = 0 are not defined by taking limits here.

**Definition 1.3 (An unread measurement on the first factor).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(\beta: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left([\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)], \left(\forall \left(u: \operatorname{Matrix.unitaryGroup}\left(\alpha, \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(\alpha \times \beta\right), \left(\alpha \times \beta\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.measureA}\left(u, \rho\right) = \operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\left(\lambda \left(i: \alpha\right) \mapsto \left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\left(\lambda \left(a: \alpha\right) \mapsto \left(\left(\operatorname{Subtype.val}\left(u\right): \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\right)\left(a, i\right)\right)\right)\right), \left(1: \operatorname{Matrix}\left(\beta, \beta, \mathbb{C}\right)\right)\right)\right)\right), \rho\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.measureA` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

The columns of the unitary u give a complete orthonormal basis on the first factor. For column i, rankOneDensity forms its outer product with its conjugate, and tensoring with the identity on the second factor gives the corresponding projector. The unread state is the sum of projector–state–projector products over all outcomes. This is the first measurement in Unifiedarxiv.tex, lines 371–382. Subtype.val explicitly exposes the complex matrix underlying the unitary.

**Definition 1.4 (An unread measurement on the second factor).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(\beta: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left([\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)], \left(\forall \left(v: \operatorname{Matrix.unitaryGroup}\left(\beta, \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(\alpha \times \beta\right), \left(\alpha \times \beta\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.measureB}\left(v, \rho\right) = \operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\left(\lambda \left(j: \beta\right) \mapsto \left(\operatorname{Matrix.kronecker}\left(\left(1: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\right), \operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\left(\lambda \left(b: \beta\right) \mapsto \left(\left(\operatorname{Subtype.val}\left(v\right): \operatorname{Matrix}\left(\beta, \beta, \mathbb{C}\right)\right)\left(b, j\right)\right)\right)\right)\right)\right)\right), \rho\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.measureB` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

The columns of the unitary v give the rank-one projectors on the second factor. Tensor each with the identity on the first factor and sum the projector–state–projector products without retaining an outcome. This is the second measurement in Unifiedarxiv.tex, lines 371–385. Subtype.val exposes the matrix underlying v.

**Definition 1.5 (Unread measurements on both factors).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(\beta: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left([\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)], \left(\forall \left(u: \operatorname{Matrix.unitaryGroup}\left(\alpha, \mathbb{C}\right)\right), \left(\forall \left(v: \operatorname{Matrix.unitaryGroup}\left(\beta, \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(\alpha \times \beta\right), \left(\alpha \times \beta\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.measureAB}\left(u, v, \rho\right) = \sum_{\left(i: \alpha\right)} \left(\operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\left(\lambda \left(j: \beta\right) \mapsto \left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\left(\lambda \left(a: \alpha\right) \mapsto \left(\left(\operatorname{Subtype.val}\left(u\right): \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\right)\left(a, i\right)\right)\right)\right), \operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\left(\lambda \left(b: \beta\right) \mapsto \left(\left(\operatorname{Subtype.val}\left(v\right): \operatorname{Matrix}\left(\beta, \beta, \mathbb{C}\right)\right)\left(b, j\right)\right)\right)\right)\right)\right)\right), \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.measureAB` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

Take the tensor product of each column projector of u with each column projector of v. The outer sum over i and the unread-state sum over j include every pair of local outcomes. This is the bilocal measurement in Unifiedarxiv.tex, lines 374–391. Both unitary-to-matrix coercions are displayed as Subtype.val.

**Definition 1.6 (Normalized entropic disturbance).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(s: \mathbb{R}\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\alpha, \alpha, \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.disturbance}\left(q, s, \sigma, \rho\right) = \frac{\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.unifiedEntropy}\left(q, s, \sigma\right) - \operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.unifiedEntropy}\left(q, s, \rho\right)}{\left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.genPurity}\left(q, \rho\right)\right)^{s}}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.disturbance` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

Subtract the original entropy from the entropy of σ and divide by the sth power of the original generalized purity. For σ equal to a measured state, this is the disturbance in equation (16), Unifiedarxiv.tex, lines 416–424. The definition itself permits arbitrary σ and ρ.

**Definition 1.7 (Correlation from measurements on the first factor).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(\beta: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left([\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)], \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(s: \mathbb{R}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(\alpha \times \beta\right), \left(\alpha \times \beta\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.correlationA}\left(q, s, \rho\right) = \operatorname{InfSet.sInf}\left(\operatorname{Set.range}\left(\left(\lambda \left(u: \operatorname{Matrix.unitaryGroup}\left(\alpha, \mathbb{C}\right)\right) \mapsto \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.disturbance}\left(q, s, \operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.measureA}\left(u, \rho\right), \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.correlationA` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

Take the real infimum of the range of disturbances over every unitary basis on the first factor. This expresses the first local correlation of equation (17), Unifiedarxiv.tex, lines 426–433, using an infimum. The definition alone makes no assertion that the infimum is attained.

**Definition 1.8 (Correlation from measurements on the second factor).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(\beta: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left([\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)], \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(s: \mathbb{R}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(\alpha \times \beta\right), \left(\alpha \times \beta\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.correlationB}\left(q, s, \rho\right) = \operatorname{InfSet.sInf}\left(\operatorname{Set.range}\left(\left(\lambda \left(v: \operatorname{Matrix.unitaryGroup}\left(\beta, \mathbb{C}\right)\right) \mapsto \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.disturbance}\left(q, s, \operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.measureB}\left(v, \rho\right), \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.correlationB` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

Take the real infimum over every unitary basis on the second factor. This is the infimum form of the second local correlation in equation (17), Unifiedarxiv.tex, lines 426–433.

**Definition 1.9 (Correlation from measurements on both factors).**

$$\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(\beta: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left([\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)], \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(s: \mathbb{R}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(\alpha \times \beta\right), \left(\alpha \times \beta\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.correlationAB}\left(q, s, \rho\right) = \operatorname{InfSet.sInf}\left(\operatorname{Set.range}\left(\left(\lambda \left(uv: \left(\operatorname{Matrix.unitaryGroup}\left(\alpha, \mathbb{C}\right) \times \operatorname{Matrix.unitaryGroup}\left(\beta, \mathbb{C}\right)\right)\right) \mapsto \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.disturbance}\left(q, s, \operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.measureAB}\left(\operatorname{Prod.fst}\left(uv\right), \operatorname{Prod.snd}\left(uv\right), \rho\right), \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.correlationAB` (`✓ std3`).

*Citation.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

Take the real infimum over all pairs uv of local unitary bases. The projections Prod.fst and Prod.snd select the two bases from the same pair. This is the infimum form of the bilocal correlation in equation (17), Unifiedarxiv.tex, lines 426–433.

**Definition 1.10 (The universal triangle-like inequality).**

$$\left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.claim}\right) \Leftrightarrow \left(\forall \left(q: \mathbb{R}\right), \left(\forall \left(s: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < q\right) \to \left(\left(q \ne \left(1: \mathbb{R}\right)\right) \to \left(\left(s \ne \left(0: \mathbb{R}\right)\right) \to \left(\forall \left(\alpha: \operatorname{Type}\right), \left(\forall \left(\beta: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], \left([\operatorname{Fintype}\left(\beta\right)] [\operatorname{DecidableEq}\left(\beta\right)], \left(\forall \left(\rho: \operatorname{Matrix}\left(\left(\alpha \times \beta\right), \left(\alpha \times \beta\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \to \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = \left(1: \mathbb{C}\right)\right) \to \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.correlationAB}\left(q, s, \rho\right) \le \operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.correlationA}\left(q, s, \rho\right) + \operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.correlationB}\left(q, s, \rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

The proposition asks whether the bilocal correlation is at most the sum of the two unilocal correlations for every q > 0 with q ≠ 1, every s ≠ 0 and every positive trace-one matrix on a product of finite complex coordinate spaces. It interprets equation (38), Unifiedarxiv.tex, lines 697–701, universally over the defined two-parameter entropy family. The question for other entropic measures appears at lines 940–951. The quantified types need only be finite and have decidable equality; they are not separately required to be inhabited. The trace equation is an equality in the complex numbers.

**Theorem 1.11 (A two-qubit counterexample).**

$$\neg \left(\operatorname{D5.S3.Entropy.UnifiedEntropyTriangleRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bosyk-et-al-2016-unified-entropy-triangle-refutation` (refuted) by `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bosyk-et-al-2016-unified-entropy-triangle-refutation","declaration_gid":"D5/S3/Entropy/UnifiedEntropyTriangleRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* G. M. Bosyk, G. Bellomo, S. Zozor, M. Portesi and P. W. Lamberti (2016). *Unified entropic measures of quantum correlations induced by local measurements*. DOI: [10.1016/j.physa.2016.06.131](https://doi.org/10.1016/j.physa.2016.06.131). URL: <https://arxiv.org/abs/1604.00329v1>.

*Commentary.*

On the coordinate basis 00, 01, 10, 11, let ρ₀ be one sixteenth of the real symmetric matrix with rows (6,1,1,0), (1,2,0,1), (1,0,2,1), (0,1,1,6), regarded as a complex matrix. It is Hermitian. For every complex coordinate vector z, sixteen times z*ρ₀z is |z₀₀+z₀₁|² + |z₀₀+z₁₀|² + |z₀₁+z₁₁|² + |z₁₀+z₁₁|² + 4|z₀₀|² + 4|z₁₁|². Each summand is nonnegative, so ρ₀ is positive semidefinite. Its trace is (6+2+2+6)/16 = 1, and its purity is Tr(ρ₀²) = 11/32.

For a Hermitian matrix σ the spectral square is the matrix square. At q = 2 and s = -1 the entropy is the inverse purity minus one. For Hermitian σ and ρ with nonzero original purity, the normalized disturbance therefore equals Re Tr(ρ²) / Re Tr(σ²) - 1.

For any unitary qubit basis, its first column projector is Hermitian, trace one and idempotent. The Bloch representation consequently expresses it as (I+n·σ)/2 for a real unit vector n. The two column projectors sum to I, so the second projector is the complement of the first. Apply this construction to u and v to obtain unit vectors n and m. Here σ in the Bloch expression denotes the three Pauli matrices. All three measured states are Hermitian: each tensor projector is Hermitian, conjugating the Hermitian state by it preserves Hermiticity, and finite sums preserve Hermiticity.

Expand the unread measurements as finite sums of projector–state–projector products. The traces of the squares (the purities) of the first and second measured states are respectively (1 + 1/16 + n(0)²/16 + n(2)²/4)/4 and (1 + 1/16 + m(0)²/16 + m(2)²/4)/4. For the bilocal measurement the trace of the square is (1 + (n(0)²+m(0)²)/16 + n(2)²m(2)²/4)/4. These identities follow by expanding the two outcomes on each factor and using n(2)² = 1-n(0)²-n(1)² and m(2)² = 1-m(0)²-m(1)².

The unit-vector identities bound each unilocal purity between 1/4 and 21/64. For the joint term, n(2)² ≤ 1-n(0)² and m(2)² ≤ 1-m(0)² give n(2)²m(2)² ≤ (1-n(0)²)(1-m(0)²). Together with 0 ≤ n(0)² ≤ 1 and 0 ≤ m(0)² ≤ 1, this bounds the bilocal purity between 1/4 and 5/16. Direct evaluation at u = v = I attains both unilocal upper bounds 21/64 and the bilocal upper bound 5/16.

Since every measured purity is positive, substituting the upper bounds into (11/32)/Re Tr(σ²)-1 bounds every unilocal disturbance below by 1/21 and every bilocal disturbance below by 1/10. The identity bases attain these lower bounds. Each bound is therefore the least element of its disturbance range, hence its real infimum. Thus correlationA 2 (-1) ρ₀ = correlationB 2 (-1) ρ₀ = 1/21, whereas correlationAB 2 (-1) ρ₀ = 1/10.

If the universal proposition held, apply it at q = 2, s = -1, α = β = Fin 2 and ρ = ρ₀. The parameter conditions, positivity and trace-one condition all hold. It would give 1/10 ≤ 1/21 + 1/21, which is false because their difference is 1/210 > 0. The universal proposition is therefore false. This counterexample concerns the nonlimiting unified entropy at (2,-1); it does not assert a classification of other indices.

## References

- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.claim`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.correlationA`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.correlationAB`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.correlationB`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.disturbance`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.genPurity`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.measureA`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.measureAB`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.measureB`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.result`
- Truth anchor: `D5/S3/Entropy/UnifiedEntropyTriangleRefutation.unifiedEntropy`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Quantum/Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Quantum/Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Quantum/Matrix/SpectralPower.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../Quantum/PureState/PureStateHandshake.md)
