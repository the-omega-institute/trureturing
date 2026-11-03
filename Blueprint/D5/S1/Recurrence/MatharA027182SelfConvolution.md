# Mathar and Kimberling's self-convolution recurrence

## Abstract

The central self-convolution of the four-diamondized Pascal row satisfies the six-term recurrence in OEIS A027182.

**Definition 1.1 (The four binomial coefficients).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; t\left(n, k\right) = \operatorname{Nat}.\operatorname{choose}\left(n + 2, k + 1\right) + \operatorname{Nat}.\operatorname{choose}\left(n + 1, k\right) + \operatorname{Nat}.\operatorname{choose}\left(n + 1, k + 1\right) + \operatorname{Nat}.\operatorname{choose}\left(n, k\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA027182SelfConvolution.t` (`✓ std3`).

*Citation.* R. J. Mathar and Clark Kimberling (2026). *OEIS A027182: self-convolution of the four-diamondized Pascal row*. URL: <https://oeis.org/A027182>.

*Commentary.*

OEIS A027170, revision 32, definition (unpaginated): "Triangular array T read by rows (4-diamondization of Pascal's triangle). Step 1: t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k). Step 2: T(n,k) = t(n,k) - t(0,0) + 1. Domain: 0 <= k <= n, n >= 0." The indices n and k are natural numbers, and Nat.choose is the ordinary binomial coefficient.

**Definition 1.2 (The diamondized row).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; T\left(n, k\right) = t\left(n, k\right) - t\left(0, 0\right) + 1$$

*Formalization.* `D5/S1/Recurrence/MatharA027182SelfConvolution.T` (`✓ std3`).

*Citation.* R. J. Mathar and Clark Kimberling (2026). *OEIS A027182: self-convolution of the four-diamondized Pascal row*. URL: <https://oeis.org/A027182>.

*Commentary.*

OEIS A027170, revision 32, definition (unpaginated): "Triangular array T read by rows (4-diamondization of Pascal's triangle). Step 1: t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k). Step 2: T(n,k) = t(n,k) - t(0,0) + 1. Domain: 0 <= k <= n, n >= 0." The subtraction is natural subtraction; the stated row domain is 0 <= k <= n. The formula defines a total natural-valued function.

**Definition 1.3 (The row polynomial).**

$$\forall n \in \mathbb{N},\; g\left(n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} \operatorname{Polynomial}.\operatorname{C}\left(T\left(n, k\right)\right) \cdot \operatorname{Polynomial}.\operatorname{X}^{k}$$

*Formalization.* `D5/S1/Recurrence/MatharA027182SelfConvolution.g` (`✓ std3`).

*Citation.* R. J. Mathar and Clark Kimberling (2026). *OEIS A027182: self-convolution of the four-diamondized Pascal row*. URL: <https://oeis.org/A027182>.

*Commentary.*

OEIS A027182, revision 8, name and comment (unpaginated): "a(n) = self-convolution of row n of array T given by A027170." "Let g(x) = Sum_(k=0..n) A027170(n,k)*x^k be the generating function of row n, then a(n) = [x^n] g(x)^2. - R. J. Mathar, May 06 2026" The polynomial has natural coefficients. Finset.range(n+1) includes both row endpoints 0 and n; Polynomial.C and Polynomial.X form each monomial.

**Definition 1.4 (The central coefficient of the square).**

$$\forall n \in \mathbb{N},\; a\left(n\right) = \operatorname{Polynomial}.\operatorname{coeff}\left(g\left(n\right)^{2}, n\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA027182SelfConvolution.a` (`✓ std3`).

*Citation.* R. J. Mathar and Clark Kimberling (2026). *OEIS A027182: self-convolution of the four-diamondized Pascal row*. URL: <https://oeis.org/A027182>.

*Commentary.*

OEIS A027182, revision 8, name and comment (unpaginated): "a(n) = self-convolution of row n of array T given by A027170." "Let g(x) = Sum_(k=0..n) A027170(n,k)*x^k be the generating function of row n, then a(n) = [x^n] g(x)^2. - R. J. Mathar, May 06 2026" Polynomial.coeff extracts the coefficient with natural index n. The source sequence starts at 1; the same expression defines a(0)=1.

**Definition 1.5 (The conjectured recurrence).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 6 \le n \Rightarrow (2 \cdot ((n : \mathbb{Z}) + 2) \cdot (a\left(n\right) : \mathbb{Z}) + (-17 \cdot (n : \mathbb{Z}) - 23) \cdot (a\left(n - 1\right) : \mathbb{Z}) + (47 \cdot (n : \mathbb{Z}) + 36) \cdot (a\left(n - 2\right) : \mathbb{Z}) + 2 \cdot (-22 \cdot (n : \mathbb{Z}) - 17) \cdot (a\left(n - 3\right) : \mathbb{Z}) + 4 \cdot (-(n : \mathbb{Z}) + 20) \cdot (a\left(n - 4\right) : \mathbb{Z}) + 8 \cdot (2 \cdot (n : \mathbb{Z}) - 9) \cdot (a\left(n - 5\right) : \mathbb{Z}) + 24 \cdot (12 \cdot (n : \mathbb{Z}) - 47) = 0))$$

*Formalization.* `D5/S1/Recurrence/MatharA027182SelfConvolution.claim` (`✓ std3`).

*Citation.* R. J. Mathar and Clark Kimberling (2026). *OEIS A027182: self-convolution of the four-diamondized Pascal row*. URL: <https://oeis.org/A027182>.

*Commentary.*

OEIS A027182, revision 8, FORMULA field (unpaginated): "Conjecture: D-finite with recurrence 2*(n+2)*a(n) +(-17*n-23)*a(n-1) +(47*n+36)*a(n-2) +2*(-22*n-17)*a(n-3) +4*(-n+20)*a(n-4) +8*(2*n-9)*a(n-5) +24*(12*n-47)=0. - R. J. Mathar, May 06 2026" The proposition ranges over every natural n with 6 <= n. Sequence indices use natural subtraction. Each sequence value and n are cast to the integers before coefficient arithmetic. The proposition asserts the displayed recurrence; no separate D-finiteness predicate is asserted.

**Theorem 1.6 (The recurrence holds).**

$$\forall n \in \mathbb{N},\; 6 \le n \Rightarrow (2 \cdot ((n : \mathbb{Z}) + 2) \cdot (a\left(n\right) : \mathbb{Z}) + (-17 \cdot (n : \mathbb{Z}) - 23) \cdot (a\left(n - 1\right) : \mathbb{Z}) + (47 \cdot (n : \mathbb{Z}) + 36) \cdot (a\left(n - 2\right) : \mathbb{Z}) + 2 \cdot (-22 \cdot (n : \mathbb{Z}) - 17) \cdot (a\left(n - 3\right) : \mathbb{Z}) + 4 \cdot (-(n : \mathbb{Z}) + 20) \cdot (a\left(n - 4\right) : \mathbb{Z}) + 8 \cdot (2 \cdot (n : \mathbb{Z}) - 9) \cdot (a\left(n - 5\right) : \mathbb{Z}) + 24 \cdot (12 \cdot (n : \mathbb{Z}) - 47) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA027182SelfConvolution.result` (`✓ std3`). ∎

*Resolves.* `Problems/mathar-a027182` (proved) by `D5/S1/Recurrence/MatharA027182SelfConvolution.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathar-a027182","declaration_gid":"D5/S1/Recurrence/MatharA027182SelfConvolution.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar and Clark Kimberling (2026). *OEIS A027182: self-convolution of the four-diamondized Pascal row*. URL: <https://oeis.org/A027182>.

*Commentary.*

Symmetry of the row turns its central self-convolution into a sum of squares. Vandermonde's identity evaluates the square and mixed binomial sums. The resulting closed form is a combination of three consecutive central binomial coefficients, an exponential and an affine term. Four consecutive central-binomial identities give an order-two recurrence for that combination. A shifted operator factorization then yields the six-term recurrence.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA027182SelfConvolution.T`
- Truth anchor: `D5/S1/Recurrence/MatharA027182SelfConvolution.a`
- Truth anchor: `D5/S1/Recurrence/MatharA027182SelfConvolution.claim`
- Truth anchor: `D5/S1/Recurrence/MatharA027182SelfConvolution.g`
- Truth anchor: `D5/S1/Recurrence/MatharA027182SelfConvolution.result`
- Truth anchor: `D5/S1/Recurrence/MatharA027182SelfConvolution.t`
