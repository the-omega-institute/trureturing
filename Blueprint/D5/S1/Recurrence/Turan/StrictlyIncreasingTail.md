# A Weighted Turan Tail for Increasing Recurrences

## Abstract

A strict off-diagonal increase and monotone diagonal give a weighted Turan bound on the complete closed right tail.

The sequence uses q(0)=1, q(1)=(t-b(0))/a(1), and a(j+2)q(j+2)=(t-b(j+1))q(j+1)-a(j+1)q(j). The theorem requires a(0)=0, strict increase of a, and monotonicity of b. Its conclusion applies to every n at least one and every t at or to the right of b(n)-2a(n). The coefficient of the neighbor product is a(n+1)/a(n), which is greater than one; this is a weighted, non-strict conclusion.

**Definition 1.1 (The canonical unit-normalized recurrence).**

$$\begin{aligned}q\left(0\right) = 1\\q\left(1\right) = \frac{t - b\left(0\right)}{a\left(1\right)}\\a\left(j + 2\right) \cdot q\left(j + 2\right) = \left(t - b\left(j + 1\right)\right) \cdot q\left(j + 1\right) - a\left(j + 1\right) \cdot q\left(j\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Turan/StrictlyIncreasingTail.orthonormal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ilia Krasikov (2011). *Turán inequalities for three-term recurrences with monotonic coefficients*. DOI: [10.1016/j.jat.2011.04.007](https://doi.org/10.1016/j.jat.2011.04.007). URL: <https://arxiv.org/html/1101.3204v1>.

*Commentary.*

This is the actual c=1 recurrence, with initial value one. The coefficients a and b are arbitrary real sequences; positivity enters through the theorem hypotheses rather than the definition.

**Theorem 1.2 (Weighted nonnegativity on the right tail).**

$$\forall a, b: \mathbb{N} \to \mathbb{R}, t: \mathbb{R}, a\left(0\right) = 0 \Rightarrow StrictMono\left(a\right) \Rightarrow Monotone\left(b\right) \Rightarrow \forall n: \mathbb{N}, 1 \le n \Rightarrow b\left(n\right) - 2 \cdot a\left(n\right) \le t \Rightarrow 0 \le orthonormal\left(a, b, t, n\right)^{2} - \frac{a\left(n + 1\right)}{a\left(n\right)} \cdot orthonormal\left(a, b, t, n - 1\right) \cdot orthonormal\left(a, b, t, n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Turan/StrictlyIncreasingTail.weighted_turan_nonneg_of_strict_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ilia Krasikov (2011). *Turán inequalities for three-term recurrences with monotonic coefficients*. DOI: [10.1016/j.jat.2011.04.007](https://doi.org/10.1016/j.jat.2011.04.007). URL: <https://arxiv.org/html/1101.3204v1>.

*Commentary.*

The base case scales the determinant to a nonnegative square. The central range is a sum of squares with nonnegative coefficient. In the farther right tail, strong induction compares successive weighted determinants through a positive factor; the residual quadratic is nonnegative because its discriminant factors as a strictly negative product under strict growth of a. This is live content beyond an instance of the published theorem. GStrict and VTail call this result directly and separately obtain strict unweighted inequalities.

## References

- Truth anchor: `D5/S1/Recurrence/Turan/StrictlyIncreasingTail.orthonormal`
- Truth anchor: `D5/S1/Recurrence/Turan/StrictlyIncreasingTail.weighted_turan_nonneg_of_strict_mono`
