# Finite Prime-Precision Window Error

## Abstract

Finite prime and precision truncation has horizontal-plus-vertical error.

**Theorem 1.1 (Finite prime-precision windows have a uniform two-part error).**

$$\begin{gathered}\forall s: \mathbb{R}, F: \operatorname{Finset}\left(\mathbb{P}\right),\\{}K: \mathbb{P} \to \mathbb{N},\\{}d, dK: \mathbb{P} \to \mathbb{R},\\{}(1 < s) \land (\forall p \in \mathbb{P}, 0 \leq \operatorname{d}\left(p\right) \leq 1) \land\\{}(\forall p \in F, 0 \leq \operatorname{d}\left(p\right) - \operatorname{dK}\left(p\right) \leq p^{-\operatorname{K}\left(p\right)}) \Rightarrow\\{}(0 \leq \frac{\sum_{p \in \mathbb{P}} p^{-s} \operatorname{d}\left(p\right)}{\sum_{p \in \mathbb{P}} p^{-s}} - \frac{\sum_{p \in F} p^{-s} \operatorname{dK}\left(p\right)}{\sum_{p \in \mathbb{P}} p^{-s}}) \land\\{}(\frac{\sum_{p \in \mathbb{P}} p^{-s} \operatorname{d}\left(p\right)}{\sum_{p \in \mathbb{P}} p^{-s}} - \frac{\sum_{p \in F} p^{-s} \operatorname{dK}\left(p\right)}{\sum_{p \in \mathbb{P}} p^{-s}} \leq \frac{\sum_{p \in \mathbb{P} \setminus F} p^{-s} + \sum_{p \in F} p^{-(s + \operatorname{K}\left(p\right))}}{\sum_{p \in \mathbb{P}} p^{-s}}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/FinitePrimePrecisionWindowError.finite_prime_precision_window_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed pair of points, d is its exact local prime distance and dK is the precision-truncated local distance. The public local laws state both the unit diameter and the precision error.

The global expression and its finite window are constructed directly from the prime weights. Splitting the convergent prime sum across F leaves the omitted-prime tail, while the local bound contributes the precision tail on F.

Mathlib's prime rpow summability theorem supplies convergence exactly for s greater than one, and positivity of the prime-weight sum justifies the common normalization.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/FinitePrimePrecisionWindowError.finite_prime_precision_window_error`
