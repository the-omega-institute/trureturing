# Resolved-count weak values

## Abstract

Every resolved coherent-state weak value differs from the no-click value by the count times the single-photon weak value.

**Definition 1.1 (The all-count proposition).**

$$\operatorname{claim} = \forall (k : \mathbb{N}), (\forall (A : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right)\right)), (\forall (B : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right)\right)), (\forall (alpha : \mathbb{C}), ((alpha \ne 0) \Rightarrow (\forall (m : \mathbb{N}), (\forall (hM : \operatorname{coherentProbability}\left(A, B, alpha, m\right) \ne 0), (\exists (hZero : \operatorname{coherentProbability}\left(A, B, alpha, 0\right) \ne 0), (\operatorname{ite}\left(m = 0, \operatorname{coherentWeakValue}\left(A, B, alpha, m, hM\right) - \operatorname{coherentWeakValue}\left(A, B, alpha, 0, hZero\right) = 0, \exists (hOne : \operatorname{singleProbability}\left(A, B, (1 : \operatorname{Fin}\left(2\right))\right) \ne 0), (\operatorname{coherentWeakValue}\left(A, B, alpha, m, hM\right) - \operatorname{coherentWeakValue}\left(A, B, alpha, 0, hZero\right) = ((m : \mathbb{C})) \cdot (\operatorname{singleWeakValue}\left(A, B, (1 : \operatorname{Fin}\left(2\right)), hOne\right)))\right)))))))))$$

*Formalization.* `D5/S3/Quantum/ResolvedCountWeakValue.claim` (`✓ std3`).

*Citation.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Section V, page 6: "This supports earlier approximate results which suggested that if a photon-number resolving detector were used, the weak value post-selected on detecting m photons would exceed the no-click weak value by precisely m times the single-photon number. We leave a rigorous proof of this conjecture for future work." The encoding has k+1 modes, with mode 0 probed and detected; A and B are arbitrary passive evolutions. Alpha is nonzero, m is a natural count, and all conditional values require nonzero probabilities. For m=0 the difference is zero without a single-photon denominator.

**Theorem 1.2 (The resolved-count identity).**

$$\forall (k : \mathbb{N}), (\forall (A : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right)\right)), (\forall (B : \operatorname{LinearIsometryEquiv}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k + 1\right)\right)\right)), (\forall (alpha : \mathbb{C}), ((alpha \ne 0) \Rightarrow (\forall (m : \mathbb{N}), (\forall (hM : \operatorname{coherentProbability}\left(A, B, alpha, m\right) \ne 0), (\exists (hZero : \operatorname{coherentProbability}\left(A, B, alpha, 0\right) \ne 0), (\operatorname{ite}\left(m = 0, \operatorname{coherentWeakValue}\left(A, B, alpha, m, hM\right) - \operatorname{coherentWeakValue}\left(A, B, alpha, 0, hZero\right) = 0, \exists (hOne : \operatorname{singleProbability}\left(A, B, (1 : \operatorname{Fin}\left(2\right))\right) \ne 0), (\operatorname{coherentWeakValue}\left(A, B, alpha, m, hM\right) - \operatorname{coherentWeakValue}\left(A, B, alpha, 0, hZero\right) = ((m : \mathbb{C})) \cdot (\operatorname{singleWeakValue}\left(A, B, (1 : \operatorname{Fin}\left(2\right)), hOne\right)))\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ResolvedCountWeakValue.result` (`✓ std3`). ∎

*Resolves.* `Problems/wiseman-steinberg-hallaji-2023-resolved-count-weak-values` (proved) by `D5/S3/Quantum/ResolvedCountWeakValue.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wiseman-steinberg-hallaji-2023-resolved-count-weak-values","declaration_gid":"D5/S3/Quantum/ResolvedCountWeakValue.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. M. Wiseman, A. M. Steinberg, M. Hallaji (2023). *Obtaining a single-photon weak value from experiments using a strong (many-photon) coherent state*. DOI: [10.1116/5.0137579](https://doi.org/10.1116/5.0137579). URL: <https://arxiv.org/abs/2211.15761v2>.

*Commentary.*

Number insertion creates one excitation in the coherent field. Its detected-mode contribution is proportional to m, while the ignored modes contribute a term independent of m. Subtracting the zero-count value cancels that term; scaling the input amplitude cancels from the remaining ratio. A positive count with nonzero probability also guarantees a nonzero single-photon probability.

## References

- Truth anchor: `D5/S3/Quantum/ResolvedCountWeakValue.claim`
- Truth anchor: `D5/S3/Quantum/ResolvedCountWeakValue.result`
- Dependency: [D5/S3/Quantum/PassiveFockModel](PassiveFockModel.md)
