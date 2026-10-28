# Unique Primitive Euler Ledger

## Abstract

A constant-one integer power series has a unique locally finite primitive Euler ledger.

**Theorem 1.1 (A later Euler factor preserves earlier coefficients).**

$$\forall p: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall n: \mathbb{N}, \forall k: \mathbb{N}, \forall c: \mathbb{Z}, k < n + 1 \Rightarrow \operatorname{coeff}\left(k, p \cdot \operatorname{eulerFactor}\left(n + 1, c\right)\right) = \operatorname{coeff}\left(k, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.coeff_mul_eulerFactor_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integer power series p, multiplication by the Euler factor of degree n+1 leaves every coefficient of degree k<n+1 unchanged, for every signed exponent c. This gives coefficient stabilization in the infinite Euler series.

**Theorem 1.2 (Extending the finite Euler product).**

$$\forall c: \mathbb{N} \to \mathbb{Z}, \forall n: \mathbb{N}, \operatorname{ledgerProduct}\left(c, n + 1\right) = \operatorname{ledgerProduct}\left(c, n\right) \cdot \operatorname{eulerFactor}\left(n + 1, c\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first n+1 Euler factors are the product of the first n factors and the factor of degree n+1 with exponent c(n). This recurrence gives the finite-product differential identity.

**Theorem 1.3 (Every constant-one integer power series has one Euler ledger).**

$$\forall f\in\operatorname{PowerSeries}(\mathbb{Z}),\ \operatorname{coeff}(0, f)=1 \Rightarrow \exists! c: \mathbb{N} \to \mathbb{Z},\\\forall N, k\in\mathbb{N},\ k\leq N \Rightarrow \operatorname{coeff}(k, \prod_{0\leq n<N} (1-X^{n+1})^{(-c_n)})=\operatorname{coeff}(k, f).$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.unique_primitive_euler_ledger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a formal power series f over the integers with constant coefficient one, there is a unique integer-valued ledger c on the positive degrees. At every finite cutoff N, its first N Euler factors reproduce every coefficient through degree N.

The factor at degree n + 1 is defined coefficientwise by generalized binomial coefficients, so it is the formal series (1 - X^(n + 1))^(-c_n). Its coefficients below degree n + 1 vanish, while the coefficient at degree n + 1 is c_n. This makes the next ledger entry the exact residual coefficient.

The source notation Gamma_phi, L, and its infinite product were not defined in the atom. The formal statement therefore specializes to ordinary integer formal power series, indexes factors by positive natural degrees, and expresses local finiteness as equality on every finite coefficient truncation. This supplies the missing semantics without weakening the existence-and-uniqueness claim.

The proof uses Mathlib's power-series coefficient convolution, finite antidiagonal sums, finite products, and generalized integer binomial coefficients. Strong induction at the first differing degree proves uniqueness.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.coeff_mul_eulerFactor_of_lt`
- Truth anchor: `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.ledgerProduct_succ`
- Truth anchor: `D5/S1/Recurrence/Witt/PrimitiveEulerLedger.unique_primitive_euler_ledger`
