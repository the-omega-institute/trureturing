# Gaussian kernel coefficients and parity

## Abstract

A rational Gaussian kernel has symmetric integer weights and even paired coefficients.

**Definition 1.1 (The recursive integer array).**

$$\forall m: \mathbb{N}, (\forall k: \mathbb{N}, ((\operatorname{weight}\left(0, k\right) = 1) \land ((\operatorname{weight}\left(m + 1, 0\right) = 1) \land (\operatorname{weight}\left(m + 1, k + 1\right) = \operatorname{weight}\left(m, k + 1\right) + \operatorname{weight}\left(m + 1, k\right) + \operatorname{weight}\left(m, k\right)))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

The boundary entries are 1. Every interior entry is the sum of its west, south and southwest predecessors. All values lie in the integers.

**Theorem 1.2 (Every recursive weight is odd).**

$$\forall m: \mathbb{N}, (\forall k: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{weight}\left(m, k\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.weight_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

Nested induction gives oddness: the three predecessor entries are odd and their sum is odd.

**Definition 1.3 (The rational Gaussian kernel).**

$$\forall m: \mathbb{N}, (\operatorname{kernel}\left(m\right) = (X + C\left(\operatorname{Complex}.\operatorname{I}\right))^{m} \cdot ((1 + C\left(\operatorname{Complex}.\operatorname{I}\right) \cdot X)^{m + 1})^{-1})$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

The kernel is (X + C Complex.I)^m times the formal inverse of (1 + C Complex.I*X)^(m+1). The denominator has constant coefficient 1.

**Theorem 1.4 (Expansion of the rational kernel).**

$$\forall m: \mathbb{N}, (\forall p: \mathbb{N}, (\forall hp: p \neq 0, (\operatorname{expand}\left(p, hp, \operatorname{kernel}\left(m\right)\right) = ((X)^{p} + C\left(\operatorname{Complex}.\operatorname{I}\right))^{m} \cdot ((1 + C\left(\operatorname{Complex}.\operatorname{I}\right) \cdot (X)^{p})^{m + 1})^{-1})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.kernel_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

Replacing X by X^p commutes with the rational expression when p is nonzero.

**Theorem 1.5 (Finite coefficient extraction).**

$$\forall p: \mathbb{N}, (\forall N: \mathbb{N}, (\forall hp: p \neq 0, (\forall f: \operatorname{PowerSeries}\left(\mathbb{C}\right), (\forall s: \operatorname{Finset}\left(\mathbb{N}\right), ((\forall k: \mathbb{N}, ((p \cdot k = N) \implies (k \in s))) \implies (\operatorname{coeff}\left(N, \operatorname{expand}\left(p, hp, f\right)\right) = \sum_{k \in s} (\operatorname{if} (p \cdot k = N) \operatorname{then} \operatorname{coeff}\left(k, f\right) \operatorname{else} 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.expansion_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

A finite set containing every solution of p*k = N collects exactly the N-th coefficient of expand p hp f.

**Theorem 1.6 (Finite shifted coefficient extraction).**

$$\forall d: \mathbb{N}, (\forall p: \mathbb{N}, (\forall N: \mathbb{N}, (\forall hp: p \neq 0, ((d \leq N) \implies (\forall f: \operatorname{PowerSeries}\left(\mathbb{C}\right), (\forall s: \operatorname{Finset}\left(\mathbb{N}\right), ((\forall k: \mathbb{N}, ((d + p \cdot k = N) \implies (k \in s))) \implies (\operatorname{coeff}\left(N, (X)^{d} \cdot \operatorname{expand}\left(p, hp, f\right)\right) = \sum_{k \in s} (\operatorname{if} (d + p \cdot k = N) \operatorname{then} \operatorname{coeff}\left(k, f\right) \operatorname{else} 0)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.shifted_expansion_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

For d at most N, the coefficient of X^d times expand p hp f is the sum over d+p*k = N.

**Theorem 1.7 (Symmetric support and diagonal parity).**

$$\forall s: \operatorname{Finset}\left(\mathbb{N}\right), (\forall P: \mathbb{N} \to \mathbb{N} \to Prop, ([\operatorname{DecidableRel}\left(P\right)], (\forall m: \mathbb{N}, (\forall k: \mathbb{N}, (P\left(m, k\right) \iff P\left(k, m\right)))) \implies (\exists z: \mathbb{Z}, ((\sum_{m \in s} (\sum_{k \in s} (\operatorname{if} (P\left(m, k\right)) \operatorname{then} \operatorname{coeff}\left(k, \operatorname{kernel}\left(m\right)\right) \operatorname{else} 0)) = (z: \mathbb{C})) \land (\operatorname{Even}\left(z - \sum_{m \in s} (\operatorname{if} (P\left(m, m\right)) \operatorname{then} \operatorname{weight}\left(m, m\right) \operatorname{else} 0)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.supported_matrix_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2019). *OEIS A323689: Gaussian generating function and square parity*. URL: <https://oeis.org/A323689>.

*Commentary.*

On any finite set of natural indices, a symmetric decidable support selects an integer coefficient sum. Its difference from the supported integer diagonal sum is even. The coefficient identity is obtained by induction from the rational kernel; symmetry pairs all off-diagonal terms.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.expansion_coefficient`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.kernel`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.kernel_expansion`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.shifted_expansion_coefficient`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.supported_matrix_integral`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.weight`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity.weight_odd`
