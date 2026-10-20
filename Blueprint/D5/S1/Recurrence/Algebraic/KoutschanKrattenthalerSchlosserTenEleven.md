# Koutschan–Krattenthaler–Schlosser: TenEleven

## Abstract

The binomial determinant identities follow from a common column multiplier and triangular determinant reductions.

**Definition 1.1 (Conjecture 23, equation (10.11)).**

$$\operatorname{claim}\left(\right) = (\forall n: \mathbb{N}, 3 \le n \implies ((\operatorname{G}\left(1, 1, 0, -2, n\right) = -\frac{1}{49} \cdot \operatorname{G}\left(2, 3, 0, -6, n\right)) \land (-\frac{1}{49} \cdot \operatorname{G}\left(2, 3, 0, -6, n\right) = -\frac{2}{7} \cdot \operatorname{G}\left(6, 4, 5, -3, n - 1\right)) \land (-\frac{2}{7} \cdot \operatorname{G}\left(6, 4, 5, -3, n - 1\right) = -\frac{4}{5577} \cdot \operatorname{G}\left(7, 6, 5, -7, n - 1\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven.claim` (`✓ std3`).

*Citation.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

Page 33: “Moreover, the following identities are conjectured to hold for all n ≥ 3:” “G₁,₁,₀,−₂(n) = −(1/49) G₂,₃,₀,−₆(n) = −(2/7) G₆,₄,₅,−₃(n − 1) = −(4/5577) G₇,₆,₅,−₇(n − 1). (10.11)” Natural n encodes the matrix size; every adjacent equality is retained as a conjunct. Subtraction of natural indices is truncated at zero.

**Theorem 1.2 (The determinant identity).**

$$\forall n: \mathbb{N}, 3 \le n \implies ((\operatorname{G}\left(1, 1, 0, -2, n\right) = -\frac{1}{49} \cdot \operatorname{G}\left(2, 3, 0, -6, n\right)) \land (-\frac{1}{49} \cdot \operatorname{G}\left(2, 3, 0, -6, n\right) = -\frac{2}{7} \cdot \operatorname{G}\left(6, 4, 5, -3, n - 1\right)) \land (-\frac{2}{7} \cdot \operatorname{G}\left(6, 4, 5, -3, n - 1\right) = -\frac{4}{5577} \cdot \operatorname{G}\left(7, 6, 5, -7, n - 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The column generating functions are sums of two shifted inverse powers. Multiplication of adjacent column differences by the inverse of (1−X)(1−2X)(1−2X+2X²) preserves each finite determinant. The resulting columns agree after their initial zero blocks, so block determinants and the first-row expansion give the rational factors and size shifts.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven.result`
- Dependency: [D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG](KoutschanKrattenthalerSchlosserShiftedG.md)
