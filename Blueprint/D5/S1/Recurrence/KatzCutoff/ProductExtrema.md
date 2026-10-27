# ProductExtrema

## Abstract

Continuants, path entries and Katz cut-offs.

Natural division is truncated division on the natural numbers. val denotes the coercion of a finite index to its natural value. All vertex indices start at zero.

**Theorem 1.1 (d zero).**

$$\forall \alpha: \mathbb{R}, \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_zero` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.2 (d one).**

$$\forall \alpha: \mathbb{R}, \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(1\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_one` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.3 (d step).**

$$\forall \alpha: \mathbb{R}, \forall k: \mathbb{N}, \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(k + 2\right) = \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(k + 1\right) - (\alpha)^{2} \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_step` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Definition 1.4 (rp).**

$$\forall \alpha: \mathbb{R}, \operatorname{rp}\left(\alpha\right) = \frac{1 + \operatorname{Real.sqrt}\left(1 - 4 \cdot (\alpha)^{2}\right)}{2}$$

*Formalization.* `D5/S1/Recurrence/KatzCutoff/ProductExtrema.rp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

This function expresses the indicated continuant quantity for arbitrary parameters.

**Definition 1.5 (rm).**

$$\forall \alpha: \mathbb{R}, \operatorname{rm}\left(\alpha\right) = \frac{1 - \operatorname{Real.sqrt}\left(1 - 4 \cdot (\alpha)^{2}\right)}{2}$$

*Formalization.* `D5/S1/Recurrence/KatzCutoff/ProductExtrema.rm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

This function expresses the indicated continuant quantity for arbitrary parameters.

**Theorem 1.6 (s sq).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies ((\operatorname{Real.sqrt}\left(1 - 4 \cdot (\alpha)^{2}\right))^{2} = 1 - 4 \cdot (\alpha)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.s_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.7 (s pos).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (0 < \operatorname{Real.sqrt}\left(1 - 4 \cdot (\alpha)^{2}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.s_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.8 (rp pos).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (0 < \operatorname{rp}\left(\alpha\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.rp_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.9 (d pos).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\forall k: \mathbb{N}, 0 < \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_pos` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Theorem 8(4), page 5, gives positivity of the path continuants. The recursion also includes k = 0.

**Theorem 1.10 (d half pos).**

$$\forall k: \mathbb{N}, 0 < \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-((\frac{1}{2}: \mathbb{R}))^{2},1]\right), ![1,1]\right)\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_half_pos` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The endpoint values from Theorem 8(5), page 5, are positive at every natural index.

**Definition 1.11 (RAB).**

$$\forall \alpha: \mathbb{R}, \forall a: \mathbb{N}, \forall b: \mathbb{N}, \operatorname{RAB}\left(\alpha, a, b\right) = \frac{\alpha \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(a - 1\right) \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(b - 1\right)}{\operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(a + b - 1\right)}$$

*Formalization.* `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

This function expresses the indicated continuant quantity for arbitrary parameters.

**Theorem 1.12 (RAB closed).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\forall a: \mathbb{N}, \forall b: \mathbb{N}, (0 < a) \implies ((0 < b) \implies (\operatorname{RAB}\left(\alpha, a, b\right) = \frac{\frac{\alpha}{\operatorname{Real.sqrt}\left(1 - 4 \cdot (\alpha)^{2}\right)} \cdot ((\operatorname{rp}\left(\alpha\right))^{a} - (\operatorname{rm}\left(\alpha\right))^{a}) \cdot ((\operatorname{rp}\left(\alpha\right))^{b} - (\operatorname{rm}\left(\alpha\right))^{b})}{(\operatorname{rp}\left(\alpha\right))^{a + b} - (\operatorname{rm}\left(\alpha\right))^{a + b}}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.13 (c bounds).**

$$(0 < \frac{1}{\operatorname{Real.sqrt}\left(5\right)}) \land (\frac{1}{\operatorname{Real.sqrt}\left(5\right)} < \frac{1}{2})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.14 (RAB lt one c).**

$$\forall a: \mathbb{N}, \forall b: \mathbb{N}, (0 < a) \implies ((0 < b) \implies (\operatorname{RAB}\left(\frac{1}{\operatorname{Real.sqrt}\left(5\right)}, a, b\right) < 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB_lt_one_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.15 (aa add bb).**

$$\forall n: \mathbb{N}, \operatorname{Nat.div}\left(n, 2\right) + \operatorname{Nat.div}\left(n - 1, 2\right) = n - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.aa_add_bb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The displayed identity or inequality is used to compare the path entries and their scalar crossing.

**Theorem 1.16 (RAB half gt one for indices).**

$$\forall n: \mathbb{N}, (6 \le n) \implies (1 < \operatorname{RAB}\left(\frac{1}{2}, \operatorname{Nat.div}\left(n, 2\right), \operatorname{Nat.div}\left(n - 1, 2\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB_half_gt_one_for_indices` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Lemma 18, page 16, gives the endpoint crossing inequality at the central split for n ≥ 6.

**Theorem 1.17 (c rec).**

$$\forall \alpha: \mathbb{R}, \forall k: \mathbb{N}, \operatorname{Nat.casesOn}\left(k + 2, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right) = \operatorname{Nat.casesOn}\left(k + 1, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right) - (\alpha)^{2} \cdot \operatorname{Nat.casesOn}\left(k, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_rec` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Theorem 8(1), page 4, gives the continuant recurrence. The zero extension includes the initial index.

**Theorem 1.18 (c add).**

$$\forall \alpha: \mathbb{R}, \forall i: \mathbb{N}, \forall j: \mathbb{N}, \operatorname{Nat.casesOn}\left(i + j + 1, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right) = \operatorname{Nat.casesOn}\left(i + 1, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right) \cdot \operatorname{Nat.casesOn}\left(j + 1, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right) - (\alpha)^{2} \cdot \operatorname{Nat.casesOn}\left(i, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right) \cdot \operatorname{Nat.casesOn}\left(j, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_add` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

The shifted continuant form of Theorem 8(2), page 4, includes both initial indices.

**Theorem 1.19 (path inverse entry).**

$$\forall n: \mathbb{N}, \forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (\operatorname{val}\left(i\right) \le \operatorname{val}\left(j\right)) \implies (\left((1 - \alpha \cdot \operatorname{SimpleGraph.pathGraph}\left(n\right).adjMatrix\left(\mathbb{R}\right))^{-1}\right)\left(i, j\right) = \frac{(\alpha)^{\operatorname{val}\left(j\right) - \operatorname{val}\left(i\right)} \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(\operatorname{val}\left(i\right)\right) \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(n - 1 - \operatorname{val}\left(j\right)\right)}{\operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(n\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.path_inverse_entry` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Theorem 9 gives the path entry formula. This resolvent identity includes the diagonal and all ordered finite indices.

**Theorem 1.20 (c nonneg).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\forall k: \mathbb{N}, 0 \le \operatorname{Nat.casesOn}\left(k, 0, (fun j: \mathbb{N} \mapsto \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_nonneg` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Theorem 8(4), page 5, gives positivity of the continuants. The zero extension has value zero at its initial index.

**Theorem 1.21 (product min).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\forall i: \mathbb{N}, \forall j: \mathbb{N}, \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(i + j\right) \le \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(i\right) \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.product_min` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Theorem 8(2), page 4, and Theorem 8(4), page 5, give the endpoint product minimum at every natural split.

**Theorem 1.22 (product center).**

$$\forall \alpha: \mathbb{R}, (0 < \alpha) \implies ((\alpha < \frac{1}{2}) \implies (\forall m: \mathbb{N}, \forall k: \mathbb{N}, (k \le m) \implies (\operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(k\right) \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(m - k\right) \le \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(\operatorname{Nat.div}\left(m, 2\right)\right) \cdot \operatorname{LinearRecurrence.mkSol}\left(\operatorname{LinearRecurrence.mk}\left(2, ![-(\alpha)^{2},1]\right), ![1,1]\right)\left(m - \operatorname{Nat.div}\left(m, 2\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KatzCutoff/ProductExtrema.product_center` (`✓ std3`). ∎

*Citation.* Emily J. Evans, Amanda E. Francis and Rebecca D. Jones (2025). *Katz similarity index comparisons*. DOI: [10.48550/arXiv.2509.02874](https://doi.org/10.48550/arXiv.2509.02874). URL: <https://arxiv.org/abs/2509.02874v1>.

*Commentary.*

Proposition 14, page 13, places the largest path entry at the centre. The displayed product inequality includes every natural split.

## References

- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB_closed`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB_half_gt_one_for_indices`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.RAB_lt_one_c`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.aa_add_bb`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_add`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_bounds`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_nonneg`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.c_rec`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_half_pos`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_one`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_pos`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_step`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.d_zero`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.path_inverse_entry`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.product_center`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.product_min`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.rm`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.rp`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.rp_pos`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.s_pos`
- Truth anchor: `D5/S1/Recurrence/KatzCutoff/ProductExtrema.s_sq`
