# Koutschan–Krattenthaler–Schlosser: TenTen

## Abstract

The binomial determinant identities follow from a common column multiplier and triangular determinant reductions.

**Definition 1.1 (Conjecture 23, equation (10.10)).**

$$\operatorname{claim}\left(\right) = (\forall n: \mathbb{N}, 3 \le n \implies ((\operatorname{G}\left(3, 0, 3, 3, n\right) = \frac{2}{3} \cdot \operatorname{G}\left(0, 1, -2, -4, n + 1\right)) \land (\frac{2}{3} \cdot \operatorname{G}\left(0, 1, -2, -4, n + 1\right) = -\frac{1}{672} \cdot \operatorname{G}\left(1, 3, -2, -8, n + 1\right)) \land (-\frac{1}{672} \cdot \operatorname{G}\left(1, 3, -2, -8, n + 1\right) = \frac{1}{63} \cdot \operatorname{G}\left(5, 4, 3, -5, n\right)) \land (\frac{1}{63} \cdot \operatorname{G}\left(5, 4, 3, -5, n\right) = \frac{4}{1002001} \cdot \operatorname{G}\left(6, 6, 3, -9, n\right)) \land (\frac{4}{1002001} \cdot \operatorname{G}\left(6, 6, 3, -9, n\right) = -\frac{8}{5} \cdot \operatorname{G}\left(9, 5, 8, -2, n - 1\right))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen.claim` (`✓ std3`).

*Citation.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

Page 33: “Moreover, the following identities are conjectured to hold for all n ≥ 3:” “G₃,₀,₃,₃(n) = ⅔ G₀,₁,−₂,−₄(n + 1) = −(1/672) G₁,₃,−₂,−₈(n + 1) = (1/63) G₅,₄,₃,−₅(n) = (4/1002001) G₆,₆,₃,−₉(n) = −(8/5) G₉,₅,₈,−₂(n − 1). (10.10)” Natural n encodes the matrix size; every adjacent equality is retained as a conjunct. Subtraction of natural indices is truncated at zero.

**Theorem 1.2 (The determinant identity).**

$$\forall n: \mathbb{N}, 3 \le n \implies ((\operatorname{G}\left(3, 0, 3, 3, n\right) = \frac{2}{3} \cdot \operatorname{G}\left(0, 1, -2, -4, n + 1\right)) \land (\frac{2}{3} \cdot \operatorname{G}\left(0, 1, -2, -4, n + 1\right) = -\frac{1}{672} \cdot \operatorname{G}\left(1, 3, -2, -8, n + 1\right)) \land (-\frac{1}{672} \cdot \operatorname{G}\left(1, 3, -2, -8, n + 1\right) = \frac{1}{63} \cdot \operatorname{G}\left(5, 4, 3, -5, n\right)) \land (\frac{1}{63} \cdot \operatorname{G}\left(5, 4, 3, -5, n\right) = \frac{4}{1002001} \cdot \operatorname{G}\left(6, 6, 3, -9, n\right)) \land (\frac{4}{1002001} \cdot \operatorname{G}\left(6, 6, 3, -9, n\right) = -\frac{8}{5} \cdot \operatorname{G}\left(9, 5, 8, -2, n - 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Koutschan; Christian Krattenthaler; Michael J. Schlosser (2024). *Determinant evaluations inspired by Di Francesco's determinant for twenty-vertex configurations*. DOI: [10.1016/j.jsc.2024.102352](https://doi.org/10.1016/j.jsc.2024.102352). URL: <https://arxiv.org/abs/2401.08481v1>.

*Commentary.*

The column generating functions are sums of two shifted inverse powers. Multiplication of adjacent column differences by the inverse of (1−X)(1−2X)(1−2X+2X²) preserves each finite determinant. The resulting columns agree after their initial zero blocks, so block determinants and the first-row expansion give the rational factors and size shifts.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen.result`
- Dependency: [D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG](KoutschanKrattenthalerSchlosserShiftedG.md)
