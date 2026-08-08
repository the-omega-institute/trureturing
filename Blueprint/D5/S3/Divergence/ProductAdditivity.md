# Product Additivity of Finite Classical KL Divergence

## Abstract

Finite real-valued classical KL divergence is additive on product mass functions.

**Theorem 1.1 (Finite classical KL divergence is additive on products).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall a, b: \iota\to \mathbb{R}, a', b': \kappa\to \mathbb{R},\\(\sum_{i}a(i)=1 \land \sum_{j}a'(j)=1 \land \\(\forall i, 0<a(i) \land 0<b(i)) \land \\(\forall j, 0<a'(j) \land 0<b'(j))) \Rightarrow\\D((i, j)\mapsto a(i)a'(j)\Vert\Vert (i, j)\mapsto b(i)b'(j))=\\D(a\Vert\Vert b)+D(a'\Vert\Vert b').\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/ProductAdditivity.kl_divergence_product_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota and kappa be finite types. Let a and b be strictly positive real functions on iota, and let a' and b' be strictly positive real functions on kappa. Only a and a' are normalized: their finite sums are one. The reference functions b and b' need only be strictly positive and are not assumed normalized.

This is the finite real-valued klDivergence of ClassicalDPI, the repository's single source for the definition, evaluated genuinely on the product mass functions (i,j) -> a(i)a'(j) and (i,j) -> b(i)b'(j), not a measure-theoretic divergence. Expanding the finite product sum and applying Real.log_mul splits the logarithm; the normalizations of a and a' then leave D(a||b) + D(a'||b').

Outside this module, Mathlib's measure-valued chain rule InformationTheory.klDiv_compProd_eq_add is not used, and no bridge between the ENNReal measure divergence and this finite real sum is established here. The declaration therefore does not identify this finite divergence with any measure-valued KL divergence.

## References

- Truth anchor: `D5/S3/Divergence/ProductAdditivity.kl_divergence_product_additive`
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
