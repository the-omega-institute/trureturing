# Monotone

## Abstract

Continuants, path entries and Katz cut-offs.

Natural division is truncated division on the natural numbers. val denotes the coercion of a finite index to its natural value. All vertex indices start at zero.

**Theorem 1.1 (RAB strictMonoOn).**

$$\forall a: \mathbb{N}, \forall b: \mathbb{N}, (0 < a) \implies ((0 < b) \implies (\operatorname{StrictMonoOn}\left((fun \alpha: \mathbb{R} \mapsto \operatorname{RAB}\left(\alpha, a, b\right)), \operatorname{Set.Ioo}\left(0, \frac{1}{2}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/Monotone.RAB_strictMonoOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.2 (R strict succ).**

$$\forall n: \mathbb{N}, (6 \le n) \implies (\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\operatorname{RAB}\left(\alpha, \operatorname{Nat.div}\left(n, 2\right), \operatorname{Nat.div}\left(n - 1, 2\right)\right) < \operatorname{RAB}\left(\alpha, \operatorname{Nat.div}\left(n + 1, 2\right), \operatorname{Nat.div}\left(n + 1 - 1, 2\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/Monotone.R_strict_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

## References

- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Monotone.RAB_strictMonoOn`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/Monotone.R_strict_succ`
- Dependency: [D5/S1/Recurrence/KatzCutoff/ProductExtrema](ProductExtrema.md)
