# Weak q-Laguerre-Polya Differentiation

## Abstract

A rational cubic refutes differentiation closure of the weak q-Laguerre-Polya class.

**Definition 1.1 (Normalized q-Borel transform).**

Lean statement: `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.qBorel`

*Formalization.* `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.qBorel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(q,f) denotes the real polynomial qBorel q f. If c(k) is the ordinary coefficient of X^k in f, its image coefficient is c(k) times k! times q raised to k(k-1)/2, times (1-q)^k, divided by the product of 1-q^(j+1) for j from zero to k-1. The empty product is one. The factor k! converts ordinary coefficients to the exponential coefficients used by the normalized transform. Division is total; the claim only uses q strictly between zero and one.

**Definition 1.2 (The rational cubic).**

$$f=1+3 X+\frac{9}{2} X^{2}+\frac{7}{2} X^{3}$$

*Formalization.* `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.halfCounterexample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here f is halfCounterexample, a polynomial over the real numbers with the displayed ordinary coefficients. At q equal to one half, its normalized transform is (X+1)^3.

**Definition 1.3 (The polynomial closure assertion).**

$$A\iff\forall q\in\mathbb{R}, 0<q \Rightarrow q<1 \Rightarrow \forall f\in\mathbb{R}[X], \operatorname{Splits}\left(\operatorname{B}\left(q, f\right)\right) \Rightarrow \operatorname{Splits}\left(\operatorname{B}\left(q, f'\right)\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.Question62Claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A denotes Question62Claim. Splits means splitting into linear factors over the real numbers, including zero and constants. The prime denotes polynomial differentiation. A real polynomial belongs to the classical Laguerre-Polya class exactly when it splits over the reals. Thus differentiation closure of the entire-function weak class would imply A. This analytic interpretation is not formalized as an additional theorem here.

**Theorem 1.4 (Differentiation closure is refuted).**

$$\neg A$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.question62_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitute q equal to one half and the displayed cubic. Its transform is (X+1)^3, which splits. The transform of its derivative is 7X^2+9X+3. A real root x would force the discriminant, minus three, to equal (14x+9)^2. Square nonnegativity contradicts this equality, so the nonconstant quadratic cannot split.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.Question62Claim`
- Truth anchor: `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.halfCounterexample`
- Truth anchor: `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.qBorel`
- Truth anchor: `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.question62_refuted`
