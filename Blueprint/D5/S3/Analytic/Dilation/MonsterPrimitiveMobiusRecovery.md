# Monster Primitive Mobius Recovery

## Abstract

Mobius inversion recovers the full bivariate Monster primitive heat series.

**Theorem 1.1 (Bivariate formal Mobius recovery).**

$$\begin{aligned}\left(H_{c}\right)\left(p, q\right) := \sum_{m, n \ge 1} \operatorname{c}(mn) p^{m} q^{n},\\\left(L_{D}\right)\left(p, q\right) := -\log(\operatorname{D}(p, q)),\\\forall c \in \mathbb{N} \to \mathbb{Z}, D \in \{F \in \mathbb{Q}[[p, q]] \mid [p^{0}q^{0}]F = 1\},\; \left(L_{D}\right)\left(p, q\right) = \sum_{k\ge1} \frac{1}{k} \cdot \left(H_{c}\right)\left(p^{k}, q^{k}\right) \Rightarrow \left(H_{c}\right)\left(p, q\right) = \sum_{k\ge1} \frac{\mu(k)}{k} \cdot \left(L_{D}\right)\left(p^{k}, q^{k}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery.monster_primitive_mobius_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be the Monster coefficient function and let D be a bivariate formal power series over the rationals with constant coefficient one. The series H_c has coefficient c(mn) at p^m q^n for positive m and n, and L_D is the formal series -log D.

The hypothesis is the full bivariate formal-series identity (126.2), using simultaneous substitution of p^k and q^k. The conclusion is the boxed full-series identity (126.3), not a coefficient-family surrogate.

Positive exponent pairs are canonically equivalent to a primitive coprime ray and a positive dilation degree. Pinned Mathlib then supplies scalar divisor-sum Mobius inversion on every ray; formal power-series extensionality reassembles the bivariate equality.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery.monster_primitive_mobius_recovery`
