# Approximation numbers and strict-threshold test subspaces

## Abstract

Strict-threshold min-max lower bounds for bounded complex Hilbert operators.

**Theorem 1.1 (errors_bdd_below).**

Lean statement: `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.errors_bdd_below`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.errors_bdd_below` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, Claude Fable 5, and Claude Opus 5 (2026). *The min--max theorem for approximation numbers*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean>.

*Commentary.*

Every error in the defining family is nonnegative, so the family is bounded below. The source and target have independent universes and complex inner-product structures; completeness is not used.

**Theorem 1.2 (approximation_number_le_error).**

Lean statement: `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.approximation_number_le_error`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.approximation_number_le_error` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, Claude Fable 5, and Claude Opus 5 (2026). *The min--max theorem for approximation numbers*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean>.

*Commentary.*

Every actual bounded rank-at-most-n map R from E to F gives approximation_number T n at most norm(T minus R). Both completeness instances are absent from this infimum bound.

**Definition 1.3 (The zero-based approximation number).**

$$\forall u: \operatorname{UniverseLevel}(), \forall v: \operatorname{UniverseLevel}(), \forall E: \operatorname{Type}_{u}, \forall F: \operatorname{Type}_{v}, [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(\mathbb{C}, E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(\mathbb{C}, F)], \forall T: \operatorname{ContinuousLinearMap}(\mathbb{C}, E, F), \forall n: \mathbb{N}, \operatorname{approximationNumber}(T, n) = \operatorname{inf}_{R: \operatorname{ContinuousLinearMap}(\mathbb{C}, E, F), \operatorname{rank}(R) \leq \operatorname{natCastCardinal}(n)} \operatorname{norm}(T-R)$$

*Formalization.* `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.approximation_number` (`✓ std3`).

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, Claude Fable 5, and Claude Opus 5 (2026). *The min--max theorem for approximation numbers*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean>.

*Commentary.*

For a bounded complex-linear map T from E to F and a natural index n, a_n(T) is the real infimum of the operator-norm errors over bounded complex-linear R from the same E to the same F with cardinal rank at most n. Source and target have independent universes. The index is zero-based; no existence of a minimizing R is asserted.

**Theorem 1.4 (Independent vectors above a strict threshold).**

$$\forall u: \operatorname{UniverseLevel}(), \forall v: \operatorname{UniverseLevel}(), \forall E: \operatorname{Type}_{u}, \forall F: \operatorname{Type}_{v}, [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(\mathbb{C}, E)] [\operatorname{CompleteSpace}(E)] [\operatorname{NormedAddCommGroup}(F)] [\operatorname{InnerProductSpace}(\mathbb{C}, F)] [\operatorname{CompleteSpace}(F)], \forall T: \operatorname{ContinuousLinearMap}(\mathbb{C}, E, F), \forall n: \mathbb{N}, \forall r: \mathbb{R}, 0 \leq r \land r < \operatorname{approximationNumber}(T, n) \Rightarrow \exists s: \mathbb{R}, r < s \land \exists a: \operatorname{Fin}(n+1) \to E, \operatorname{LinearIndependent}(\mathbb{C}, a) \land \forall x: E, x \in \operatorname{span}(\mathbb{C}, \operatorname{range}(a)) \Rightarrow s \operatorname{norm}(x) \leq \operatorname{norm}(\operatorname{T}(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.exists_independent_lower_bound` (`✓ std3`). ∎

*Citation.* Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, Claude Fable 5, and Claude Opus 5 (2026). *The min--max theorem for approximation numbers*. URL: <https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean>.

*Commentary.*

The cited published proof supplies the approximation-number definition, operator modulus, spectral cutoffs and strict-threshold min-max construction. The complex specialization uses the same continuous-functional-calculus geometry and rank-versus-error argument. The source note identifies the selected files and their attribution; the accompanying third-party license packet retains the original notices. This uses published mathematics and makes no novelty claim.

Let E : Type u and F : Type v be complete normed additive groups with complex inner products, and let T : E →L[ℂ] F. For every n : ℕ and every r : ℝ satisfying 0 ≤ r and r < approximation_number T n, there exist s : ℝ with r < s and a : Fin (n + 1) → E. The family a is linearly independent over ℂ, and every x in the complex span of its range satisfies s * norm(x) ≤ norm(T x). There is no compactness, separability, finite-dimensionality, nontriviality, common-universe or index-below-dimension assumption.

Set A to the positive square root of T* T and choose r < s < a_n(T). The norm identity norm(A x) = norm(T x) transports estimates for A to T. Continuous functional calculus gives the positive parts of A - s and s - A. Their product is zero, and the cocutoff is self-adjoint. Its range lies in the cutoff kernel, so it vanishes on that kernel's orthogonal complement. Positivity and the inner-product bound yield a lower modulus s on the complement and an upper modulus s on the kernel.

If the complement has cardinal rank greater than n, it supplies n + 1 independent vectors. Otherwise its orthogonal projection P has finite rank at most n; T composed with P is an admissible bounded approximant, and the error on the complementary kernel has norm at most s. This contradicts s < a_n(T). Orthogonal projection comes from a closed Hilbert subspace; self-adjointness of a cutoff alone does not imply idempotence.

## References

- Truth anchor: `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.approximation_number`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.approximation_number_le_error`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.errors_bdd_below`
- Truth anchor: `D5/S3/HilbertOperators/Approximation/MinMaxLowerBound.exists_independent_lower_bound`
