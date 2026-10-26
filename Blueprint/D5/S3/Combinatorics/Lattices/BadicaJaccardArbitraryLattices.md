# The generalized Jaccard triangle inequality on arbitrary lattices

## Abstract

Reciprocal supermodularity gives the Jaccard triangle inequality on every lattice.

**Definition 1.1 (Strictly positive valuations).**

$$\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; \operatorname{IsStrictlyPositive}\left(f\right) = (\forall X \in L,\; 0 < \operatorname{f}\left(X\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsStrictlyPositive` (`✓ std3`).

*Citation.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Definition 3(i), p. 3: ‘If f(X) > 0 for all X ∈ L, then f is strictly positive.’

**Definition 1.2 (Supermodular valuations).**

$$\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; \operatorname{IsSupermodular}\left(f\right) = (\forall X \in L,\; \forall Y \in L,\; \operatorname{f}\left(X\right) + \operatorname{f}\left(Y\right) \le \operatorname{f}\left(\operatorname{SemilatticeSup}.\operatorname{sup}\left(X, Y\right)\right) + \operatorname{f}\left(\operatorname{SemilatticeInf}.\operatorname{inf}\left(X, Y\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsSupermodular` (`✓ std3`).

*Citation.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Definition 3(v), p. 3: ‘f is supermodular if and only if: f(X) + f(Y) ≤ f(X ∨ Y) + f(X ∧ Y) ∀X, Y ∈ L’. The symbols ⊔ and ⊓ denote the lattice join and meet.

**Definition 1.3 (Submodular valuations).**

$$\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; \operatorname{IsSubmodular}\left(f\right) = (\forall X \in L,\; \forall Y \in L,\; \operatorname{f}\left(\operatorname{SemilatticeSup}.\operatorname{sup}\left(X, Y\right)\right) + \operatorname{f}\left(\operatorname{SemilatticeInf}.\operatorname{inf}\left(X, Y\right)\right) \le \operatorname{f}\left(X\right) + \operatorname{f}\left(Y\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsSubmodular` (`✓ std3`).

*Citation.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Definition 3(iii), p. 3: ‘f is submodular if and only if: f(X) + f(Y) ≥ f(X ∨ Y) + f(X ∧ Y) ∀X, Y ∈ L’. The displayed inequality places the join and meet terms on the left.

**Definition 1.4 (Log-submodular valuations).**

$$\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; \operatorname{IsLogSubmodular}\left(f\right) = (\operatorname{IsStrictlyPositive}\left(f\right) \land \operatorname{IsSubmodular}\left(\operatorname{Real}.\operatorname{log} \circ f\right))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsLogSubmodular` (`✓ std3`).

*Citation.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Definition 3(iv), p. 3: ‘If f is strictly positive and log ∘ f is submodular, then f is log-submodular.’ Strict positivity means ‘If f(X) > 0 for all X ∈ L, then f is strictly positive.’ It is expressed by ∀ X, 0 < f X; Real.log is the real logarithm.

**Definition 1.5 (The generalized Jaccard distance).**

$$\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; \forall A \in L,\; \forall B \in L,\; \operatorname{jaccardDist}\left(f, A, B\right) = 1 - \frac{\operatorname{f}\left(\operatorname{SemilatticeInf}.\operatorname{inf}\left(A, B\right)\right)}{\operatorname{f}\left(\operatorname{SemilatticeSup}.\operatorname{sup}\left(A, B\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.jaccardDist` (`✓ std3`).

*Citation.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Equation (17), p. 5: ‘d_{f,J}(A, B) = 1 − f(A ∧ B)/f(A ∨ B)’. The quotient is real division. The formula is defined for every f; the triangle theorems assume strict positivity.

**Definition 1.6 (The second question in Section 8).**

$$claim = (\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; (\operatorname{IsStrictlyPositive}\left(f\right)) \Rightarrow ((\operatorname{Monotone}\left(f\right)) \Rightarrow ((\operatorname{IsSupermodular}\left(f\right)) \Rightarrow ((\operatorname{IsLogSubmodular}\left(f\right)) \Rightarrow (\forall A \in L,\; \forall B \in L,\; \forall C \in L,\; \operatorname{jaccardDist}\left(f, A, C\right) \le \operatorname{jaccardDist}\left(f, A, B\right) + \operatorname{jaccardDist}\left(f, B, C\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.claim` (`✓ std3`).

*Citation.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Section 8, p. 12: ‘While we established metricity for supermodular and log-submodular valuations, the proof relies on the lattice being both relatively complemented and distributive. It is still unknown whether the standard generalized Jaccard formula holds up to the triangle inequality for these valuations on arbitrary lattices that lack those two specific traits.’ Here L is an arbitrary lattice, at every universe level, f maps L to ℝ, and A, B, C range over L. Strict positivity, Monotone f, supermodularity and log-submodularity are the hypotheses. No distributivity or complementation is assumed.

**Definition 1.7 (The fourth question in Section 8).**

$$claimSufficiency = (\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; (\operatorname{IsStrictlyPositive}\left(f\right)) \Rightarrow ((\operatorname{Monotone}\left(f\right)) \Rightarrow ((\operatorname{IsSupermodular}\left(f\right)) \Rightarrow ((\operatorname{IsSupermodular}\left(\lambda (X: L) \mapsto (\operatorname{f}\left(X\right))^{-1}\right)) \Rightarrow (\forall A \in L,\; \forall B \in L,\; \forall C \in L,\; \operatorname{jaccardDist}\left(f, A, C\right) \le \operatorname{jaccardDist}\left(f, A, B\right) + \operatorname{jaccardDist}\left(f, B, C\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.claimSufficiency` (`✓ std3`).

*Citation.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Section 8, p. 12: ‘The reverse of this statement remains untested: if f and 1/f are supermodular, is that enough on its own to guarantee the triangle inequality? Also, it is unclear if the stricter log-submodularity constraint used in Theorem 2 is actually required, or if it can be loosened to match the more basic necessary conditions established later in the paper.’ The quantified statement includes strict positivity and Monotone f, as in Theorem 4; the reciprocal is the pointwise function X ↦ (f X)⁻¹.

**Theorem 1.8 (The necessary conditions suffice).**

$$\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; (\operatorname{IsStrictlyPositive}\left(f\right)) \Rightarrow ((\operatorname{Monotone}\left(f\right)) \Rightarrow ((\operatorname{IsSupermodular}\left(f\right)) \Rightarrow ((\operatorname{IsSupermodular}\left(\lambda (X: L) \mapsto (\operatorname{f}\left(X\right))^{-1}\right)) \Rightarrow (\forall A \in L,\; \forall B \in L,\; \forall C \in L,\; \operatorname{jaccardDist}\left(f, A, C\right) \le \operatorname{jaccardDist}\left(f, A, B\right) + \operatorname{jaccardDist}\left(f, B, C\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.resultSufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

Supermodularity at A ⊓ B and B ⊓ C bounds the sum of their values by f B + f (A ⊓ C). Supermodularity of the reciprocal at A ⊔ B and B ⊔ C bounds the sum of the reciprocal values by 1 / f B + 1 / f (A ⊔ C). Monotonicity also bounds each meet value by f B and each reciprocal join value by 1 / f B. Ordering the two reciprocal weights and splitting at f (A ⊓ C) ≤ f B gives the scalar estimate needed for the triangle inequality. No distributive law or complement enters this argument.

**Theorem 1.9 (Log-submodularity also suffices on every lattice).**

$$\forall L \in Type,\; [\operatorname{Lattice}\left(L\right)], \forall f \in L \to \mathbb{R},\; (\operatorname{IsStrictlyPositive}\left(f\right)) \Rightarrow ((\operatorname{Monotone}\left(f\right)) \Rightarrow ((\operatorname{IsSupermodular}\left(f\right)) \Rightarrow ((\operatorname{IsLogSubmodular}\left(f\right)) \Rightarrow (\forall A \in L,\; \forall B \in L,\; \forall C \in L,\; \operatorname{jaccardDist}\left(f, A, C\right) \le \operatorname{jaccardDist}\left(f, A, B\right) + \operatorname{jaccardDist}\left(f, B, C\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.result` (`✓ std3`). ∎

*Resolves.* `Problems/badica-2026-jaccard-arbitrary-lattices` (proved) by `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"badica-2026-jaccard-arbitrary-lattices","declaration_gid":"D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Bădică and A. Bădică (2026). *On the Triangle Inequality for the Jaccard Distance in Arbitrary Lattices*. DOI: [10.48550/arXiv.2608.18194](https://doi.org/10.48550/arXiv.2608.18194). URL: <https://arxiv.org/abs/2608.18194v1>.

*Commentary.*

For positive values, log-submodularity gives f (X ⊔ Y) · f (X ⊓ Y) ≤ f X · f Y. Combined with supermodularity, this implies supermodularity of the reciprocal function. The preceding theorem therefore proves the triangle inequality under the hypotheses of the second question. Only the triangle inequality is asserted; separation, a MetricSpace instance and the symmetric-difference question remain outside these statements.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsLogSubmodular`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsStrictlyPositive`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsSubmodular`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.IsSupermodular`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.claim`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.claimSufficiency`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.jaccardDist`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.result`
- Truth anchor: `D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.resultSufficiency`
