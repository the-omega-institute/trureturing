# Mathar's recurrence for the central-binomial transform

## Abstract

The binomial sum defining OEIS A113409 satisfies Mathar's five-term recurrence at every index at least four.

**Definition 1.1 (The literal binomial sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(\operatorname{Nat}.\operatorname{div}\left(n, 2\right) + 1\right)} \operatorname{Nat}.\operatorname{choose}\left(n - k, k\right) \cdot \operatorname{Nat}.\operatorname{choose}\left(k, \operatorname{Nat}.\operatorname{div}\left(k, 2\right)\right)$$

*Formalization.* `D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.a` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; G. C. Greubel (2012). *OEIS A113409, A transform of the central binomial coefficients A001405*. URL: <https://oeis.org/A113409>.

*Commentary.*

OEIS A113409, FORMULA field: "a(n) = Sum_{k=0..floor(n/2)} C(n-k, k)*C(k, floor(k/2))." Both indices are natural numbers. Nat.choose is the ordinary binomial coefficient, Nat.div(n,2) is floor(n/2), and Finset.range(m) contains 0 through m - 1; the upper endpoint floor(n/2) is therefore included. Subtraction in this definition is natural subtraction.

**Definition 1.2 (Mathar's conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (((n : \mathbb{Z}) + 2) \cdot (\operatorname{a}\left(n\right) : \mathbb{Z}) - 2 \cdot ((n : \mathbb{Z}) + 1) \cdot (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + ((n : \mathbb{Z}) - 4) \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + 2 \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) + 4 \cdot (2 - (n : \mathbb{Z})) \cdot (\operatorname{a}\left(n - 4\right) : \mathbb{Z}) = 0))$$

*Formalization.* `D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Paul Barry; G. C. Greubel (2012). *OEIS A113409, A transform of the central binomial coefficients A001405*. URL: <https://oeis.org/A113409>.

*Commentary.*

OEIS A113409, FORMULA field: "Conjecture: (n+2)*a(n)-2*(n+1)*a(n-1) +(n-4)*a(n-2) +2*a(n-3) +4*(2-n)*a(n-4)=0. - _R. J. Mathar_, Nov 07 2012" The entry is an online sequence record without page numbers. The encoding quantifies every natural n with 4 <= n. All five indices use natural subtraction, while n and each value a(n-j) are explicitly cast to the integers before the coefficient products and additions are evaluated.

**Theorem 1.3 (The recurrence holds).**

$$\forall n \in \mathbb{N},\; 4 \le n \Rightarrow (((n : \mathbb{Z}) + 2) \cdot (\operatorname{a}\left(n\right) : \mathbb{Z}) - 2 \cdot ((n : \mathbb{Z}) + 1) \cdot (\operatorname{a}\left(n - 1\right) : \mathbb{Z}) + ((n : \mathbb{Z}) - 4) \cdot (\operatorname{a}\left(n - 2\right) : \mathbb{Z}) + 2 \cdot (\operatorname{a}\left(n - 3\right) : \mathbb{Z}) + 4 \cdot (2 - (n : \mathbb{Z})) \cdot (\operatorname{a}\left(n - 4\right) : \mathbb{Z}) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry; G. C. Greubel (2012). *OEIS A113409, A transform of the central binomial coefficients A001405*. URL: <https://oeis.org/A113409>.

*Commentary.*

Pascal's identity relates consecutive rows of the kernel Nat.choose(n-k,k). A weighted form of the same kernel identity controls the sum with an additional factor k. Splitting Nat.choose(k,floor(k/2)) by the parity of k gives its two-step recurrence from the central-binomial recurrence. Applying the kernel to this relation and eliminating the shifted weighted sums yields the five-term recurrence by induction. Terms beyond floor(n/2) vanish, identifying the extended sum used in the proof with the defining sum a(n). No generating-function equation or asymptotic statement is asserted here.

## References

- Truth anchor: `D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.claim`
- Truth anchor: `D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.result`
