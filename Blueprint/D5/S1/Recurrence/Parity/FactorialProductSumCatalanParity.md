# Factorial Product Sum and Catalan Parity

## Abstract

The coefficients of OEIS A222013 are odd exactly one below a power of two.

The entry cited in hanna2024a222013 specifies a factorial product sum for A and conjectures that a(n) is odd exactly when n=2^k-1 for some natural k. The conjecture is dated December 6, 2024. The equivalent formulation n+1=2^k avoids natural subtraction.

All indices are natural numbers, all unreduced coefficients are integers, and X is the indeterminate. A denotes generatingSeries. The operator coeff extracts a coefficient, mk constructs a series from its coefficient function, and C embeds an integer as a constant series. The operator int casts a natural number to an integer; factorial is the natural factorial; div is natural integer division. The operator invOfUnit takes the indicated series and the integer unit 1. Each denominator factor has constant coefficient one. The product indexed by k in range(r) uses k+1, hence is exactly the product from 1 to r.

P denotes the local approximations. The finite coefficient window is exact because the rth term contains X^r; it expresses the infinite sum without an infinite-sum operation on formal series. The map pi is Int.castRingHom into ZMod(2), and map(pi,B) reduces B coefficientwise. K denotes the integer catalanSeries from CatalanCompositionSquareParity, with zero constant coefficient and K=X+K^2. Its binary_catalan theorem supplies the binary support.

**Definition 1.1 (The factorial product summand).**

$$\forall r: \mathbb{N}, \forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{term}\left(r, F\right) = \operatorname{C}\left(\operatorname{int}\left(\operatorname{factorial}\left(r\right)\right)\right) \cdot X^{r} \cdot F^{\operatorname{div}\left(r \cdot (r + 1), 2\right)} \cdot \operatorname{invOfUnit}\left(\prod_{k \in \operatorname{range}\left(r\right)} (1 + \operatorname{C}\left(\operatorname{int}\left(k + 1\right)\right) \cdot X \cdot F^{k + 1}), 1\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.term` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator is the factorial constant times X^r times the indicated power of the input series. Multiplication by invOfUnit implements division by the product with constant coefficient one.

**Definition 1.2 (The coefficient sequence).**

$$\begin{aligned}\operatorname{P}\left(0\right) = 0\\\forall n: \mathbb{N}, \operatorname{P}\left(n + 1\right) = \operatorname{mk}\left((N \mapsto \sum_{r \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, \operatorname{term}\left(r, \operatorname{P}\left(n\right)\right)\right)))\right)\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Iteration of the finite-window operator starts at the zero series. Agreement below degree n becomes agreement below degree n+1: powers, products and unit inverses preserve agreement, and every nonconstant summand adds at least one factor X. The diagonal defines a(n).

**Definition 1.3 (The integer generating series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series is constructed from the diagonal coefficient function a.

**Theorem 1.4 (The exact coefficient window).**

$$\forall r: \mathbb{N}, \forall N: \mathbb{N}, (N < r) \implies \forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{coeff}\left(N, \operatorname{term}\left(r, F\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.term_coeff_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit factor X^r divides the summand. Mathlib's coefficient criterion for this divisibility forces every coefficient below r to vanish.

**Theorem 1.5 (The OEIS equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 1) \land (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, A\right) = \sum_{r \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, \operatorname{term}\left(r, A\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stability of the approximations identifies each diagonal coefficient with the corresponding coefficient after one further iteration. This proves the defining sum and its constant coefficient one.

**Theorem 1.6 (Uniqueness of the integer solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, B\right) = \sum_{r \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, \operatorname{term}\left(r, B\right)\right))) \implies B = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two fixed points agree below degree zero. Applying degree contraction inductively gives agreement below every degree, hence equality. The coefficient equation also forces the stated normalization.

**Theorem 1.7 (Reduction to the Catalan equation).**

$$\operatorname{map}\left(pi, A\right) = 1 + X \cdot \operatorname{map}\left(pi, A\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.mod_two_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r at least two, divisibility of r! by two kills the entire summand. The remaining terms give C=1+XC invOfUnit(1+XC,1) for C=map(pi,A). Multiplication by 1+XC and characteristic two give C=1+XC^2.

**Theorem 1.8 (Identification with binary Catalan support).**

$$X \cdot \operatorname{map}\left(pi, A\right) = \operatorname{map}\left(pi, K\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.mod_two_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both X map(pi,A) and map(pi,K) have zero constant coefficient and satisfy Y=X+Y^2. Their difference times the unit 1-Y-Z is zero, so cancellation identifies the two series.

**Theorem 1.9 (Hanna's parity conjecture).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n + 1 = 2^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a222013-factorial-product-sum-catalan-parity` (proved) by `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a222013-factorial-product-sum-catalan-parity","declaration_gid":"D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2024). *OEIS A222013, g.f. A(x) = Sum n! x^n A(x)^(n(n+1)/2) / Product (1 + k x A(x)^k), parity conjecture (Dec 2024)*. URL: <https://oeis.org/A222013>.

*Commentary.*

Taking coefficient n+1 in the Catalan identity gives the reduction of a(n). The imported binary_catalan theorem says this is one precisely when n+1 is a power of two. Casting an integer to one in ZMod(2) is equivalent to oddness.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.mod_two_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.mod_two_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.term`
- Truth anchor: `D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.term_coeff_eq_zero`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)
