# Koutschan–Krattenthaler–Schlosser: ShiftedG

## Abstract

The binomial determinant identities follow from a common column multiplier and triangular determinant reductions.

**Definition 1.1 (Generalized binomial coefficients).**

$$\forall x: \mathbb{Q}, \forall p: \mathbb{Z}, \operatorname{binom}\left(x, p\right) = \operatorname{ite}\left(p < 0, 0, \operatorname{Ring}.\operatorname{choose}\left(x, \operatorname{Int}.\operatorname{toNat}\left(p\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.binom` (`✓ std3`).

*Citation.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

Page 1, (1.2): the binomial coefficient is defined by α(α−1)⋯(α−p+1)/p! for p ≥ 0, and 0 for p < 0. Here x is rational and p is an integer; Ring.choose supplies the falling-factorial expression when p is nonnegative.

**Definition 1.2 (The four-parameter determinants).**

$$\forall a: \mathbb{Z}, \forall b: \mathbb{Z}, \forall c: \mathbb{Z}, \forall d: \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{G}\left(a, b, c, d, n\right) = \operatorname{Matrix}.\operatorname{det}\left(\operatorname{Matrix}.\operatorname{of}\left(fun i j: \operatorname{Fin}\left(n\right) \mapsto (2: \mathbb{Q})^{(\operatorname{val}\left(i\right): \mathbb{Z}) + b} \cdot \operatorname{binom}\left((\operatorname{val}\left(i\right): \mathbb{Q}) + 4 \cdot (\operatorname{val}\left(j\right): \mathbb{Q}) + (c: \mathbb{Q}), 4 \cdot (\operatorname{val}\left(j\right): \mathbb{Z}) + a\right) + \operatorname{binom}\left(-(\operatorname{val}\left(i\right): \mathbb{Q}) + 4 \cdot (\operatorname{val}\left(j\right): \mathbb{Q}) + (d: \mathbb{Q}), 4 \cdot (\operatorname{val}\left(j\right): \mathbb{Z}) + a\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.G` (`✓ std3`).

*Citation.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

Page 32: “Let us denote” G_{α,β,γ,δ}(n) := det_{0≤i,j≤n−1}(2^{i+β} binom(i+4j+γ,4j+α) + binom(−i+4j+δ,4j+α)). The four parameters are integers. Rows and columns are Fin n, starting at zero; powers of 2 have integer exponents and entries lie in the rationals.

**Definition 1.3 (Conjecture 23, equation (10.12)).**

$$\operatorname{claim}\left(\right) = (\forall n: \mathbb{N}, 3 \le n \implies (\operatorname{G}\left(2, 1, 2, 0, n\right) = 2 \cdot \operatorname{G}\left(7, 4, 7, -1, n - 1\right)))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.claim` (`✓ std3`).

*Citation.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

Page 33: “Moreover, the following identities are conjectured to hold for all n ≥ 3:” “G₂,₁,₂,₀(n) = 2 G₇,₄,₇,−₁(n − 1). (10.12)” Natural n encodes the matrix size; every adjacent equality is retained as a conjunct. Subtraction of natural indices is truncated at zero.

**Theorem 1.4 (The determinant identity).**

$$\forall n: \mathbb{N}, 3 \le n \implies (\operatorname{G}\left(2, 1, 2, 0, n\right) = 2 \cdot \operatorname{G}\left(7, 4, 7, -1, n - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The column generating functions are sums of two shifted inverse powers. Multiplication of adjacent column differences by the inverse of (1−X)(1−2X)(1−2X+2X²) preserves each finite determinant. The resulting columns agree after their initial zero blocks, so block determinants and the first-row expansion give the rational factors and size shifts.

**Lemma 1.5 (link BC).**

$$\forall n: \mathbb{N}, 3 \le n \implies (\operatorname{G}\left(1, 3, -2, -8, n\right) = -448 \cdot \operatorname{G}\left(0, 1, -2, -4, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_BC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

**Lemma 1.6 (link PD).**

$$\forall n: \mathbb{N}, 2 \le n \implies (\operatorname{G}\left(5, 4, 3, -5, n\right) = 63 \cdot \operatorname{G}\left(3, 0, 3, 3, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_PD` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

**Lemma 1.7 (link PE).**

$$\forall n: \mathbb{N}, 3 \le n \implies (\operatorname{G}\left(6, 6, 3, -9, n\right) = \frac{1002001}{4} \cdot \operatorname{G}\left(3, 0, 3, 3, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_PE` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

**Lemma 1.8 (link TF).**

$$\forall n: \mathbb{N}, 1 \le n \implies (\operatorname{G}\left(8, 3, 8, 2, n\right) = -\frac{4}{5} \cdot \operatorname{G}\left(9, 5, 8, -2, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_TF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

**Lemma 1.9 (link HI).**

$$\forall n: \mathbb{N}, 2 \le n \implies (\operatorname{G}\left(1, 1, 0, -2, n\right) = -\frac{1}{49} \cdot \operatorname{G}\left(2, 3, 0, -6, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_HI` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

**Lemma 1.10 (link VJ).**

$$\forall n: \mathbb{N}, 1 \le n \implies (\operatorname{G}\left(5, 2, 5, 1, n\right) = \frac{1}{7} \cdot \operatorname{G}\left(6, 4, 5, -3, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_VJ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

**Lemma 1.11 (link VK).**

$$\forall n: \mathbb{N}, 2 \le n \implies (\operatorname{G}\left(5, 2, 5, 1, n\right) = \frac{2}{5577} \cdot \operatorname{G}\left(7, 6, 5, -7, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_VK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

**Lemma 1.12 (prop H).**

$$\forall n: \mathbb{N}, \operatorname{G}\left(1, 1, 0, -2, n + 1\right) = -2 \cdot \operatorname{G}\left(5, 2, 5, 1, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.prop_H` (`✓ std3`). ∎

*Citation.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

Page 32, Proposition 22: “For all integers n ≥ 2 we have the following relations:” “G₁,₁,₀,−₂(n) = −2 G₅,₂,₅,₁(n − 1), (10.3)” Replacing the source size by n+1 gives the displayed formula; its first-row reduction also covers size one.

**Lemma 1.13 (prop B).**

$$\forall n: \mathbb{N}, \operatorname{G}\left(0, 1, -2, -4, n + 2\right) = 3 \cdot \operatorname{G}\left(8, 3, 8, 2, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.prop_B` (`✓ std3`). ∎

*Citation.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

Page 32, Proposition 22: “For all integers n ≥ 2 we have the following relations:” “G₀,₁,−₂,−₄(n) = 3 G₄,₂,₃,−₁(n − 1) = 3 G₈,₃,₈,₂(n − 2), (10.2)” Replacing the source size by n+2 gives the displayed formula after two first-row reductions.

**Lemma 1.14 (p shift all).**

$$\forall n: \mathbb{N}, \operatorname{G}\left(3, 0, 3, 3, n + 1\right) = 2 \cdot \operatorname{G}\left(8, 3, 8, 2, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.p_shift_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.G`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.binom`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_BC`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_HI`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_PD`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_PE`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_TF`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_VJ`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.link_VK`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.p_shift_all`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.prop_B`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.prop_H`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.result`
