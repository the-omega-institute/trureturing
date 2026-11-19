---
bibkey: haah2019productdecomposition
authors: Jeongwan Haah
year: 2019
title: "Product Decomposition of Periodic Functions in Quantum Signal Processing"
doi: 10.22331/q-2019-10-07-190
url: https://arxiv.org/abs/1806.10236v4
claim: "Theorem 2 gives the unique exact-length ordered rank-one-projector factorization of arbitrary parity-controlled special-unitary Laurent loops of actual degree n, together with the forward product class assertion."
strata_touched:
  - D5/S3/ContinuousObservables/LaurentLoopFactorization
license: citation-only
triage: anchor
---

## Verified locator

DOI: `10.22331/q-2019-10-07-190`; source: <https://arxiv.org/abs/1806.10236v4>; primitive equation (2), printed page 3, and Definition 1/Theorem 2, printed pages 4–5.

# Exact ordered factorization of special-unitary Laurent loops

The primary version is [arXiv:1806.10236v4](https://arxiv.org/abs/1806.10236v4).
Equation (2), printed page 3, defines the primitive matrix

$$E_P(t)=tP+t^{-1}(I-P).$$

Definition 1 and Theorem 2, printed pages 4–5, concern arbitrary finitely supported two-by-two complex matrix coefficients. The class $E_n$ has support in $[-n,n]$, exponents congruent to $n$ modulo two, and values in $SU(2)$ on the entire unit circle. Actual degree $n$ means $C_n\ne0$ or $C_{-n}\ne0$.

Every product of $n$ rank-one orthogonal primitive factors lies in $E_n$. Conversely, every member of $E_n$ of actual degree $n$ has a unique pair consisting of an arbitrary constant $E_0\in SU(2)$ and an ordered list of exactly $n$ rank-one orthogonal projectors, such that

$$F(t)=E_0E_{P_1}(t)\cdots E_{P_n}(t).$$

The equality is a Laurent polynomial identity. No additional reciprocity, inversion or equatorial constraint is imposed. At $n=0$ the list is empty and every special-unitary constant is permitted. The forward assertion does not give actual degree $n$ for a padded product.

The proof determines the last projector from the raw endpoints. When $C_n\ne0$, it is $C_n^\dagger C_n/\operatorname{Tr}(C_n^\dagger C_n)$. When the positive endpoint vanishes, the nonzero negative endpoint gives its complementary projection. Multiplication on the right by the inverse primitive factor lowers the actual degree by exactly one and preserves the class. Recursion gives existence; the uniquely determined last projection and cancellation give ordered uniqueness.

The formal statement covers this algebraic theorem. Numerical stability, an efficient synthesis algorithm, scalar completion, query complexity and physical implementation are outside its conclusion. No external Lean proof source is incorporated.
