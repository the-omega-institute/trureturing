---
bibkey: tauceti2026physicalorthonormality
authors: The Tau Ceti contributors
year: 2026
title: Physical product Hermite orthonormal integrals
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd
claim: The displayed normalized physical Hermite products have actual Euclidean Lebesgue Kronecker integrals in every natural dimension and at all positive physical parameters.
strata_touched:
  - D5/S3/Quantum/Analysis/Hermite/PhysicalProductOrthonormality
license: Apache-2.0
triage: anchor
---

# Physical product Hermite orthonormal integrals

Source: The Tau Ceti contributors, TauCetiProject/TauCeti,
revision `f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd` (Apache-2.0).
The receiving source credits the Hermite lowering and weighted integration-by-parts
construction in the following donor modules at that revision:

- `RingTheory/Polynomial/Hermite/Derivative.lean`;
- `Analysis/SpecialFunctions/Hermite/Orthogonality.lean`;
- `Analysis/SpecialFunctions/Hermite/Function/Orthonormal.lean`.

The physical rescaling and actual product-volume transport are constructions
for the displayed functions below. The donor argument carries no claim of
research originality by this adaptation. Its copyright remains in the receiving
Lean source; the full license is in
`docs/reports/hermite-suppliers/tauceti-LICENSE.txt`.

## Exact physical integral statement

**定理 1.1（物理乘积 Hermite 的实际积分正交归一性）。** 对每个自然数 $d\in\mathbb N$，在 $E_d=\mathrm{EuclideanSpace}\;\mathbb R\;(\mathrm{Fin}\,d)$ 上取实际 Euclidean Lebesgue 体积。取 $\hbar>0$ 与函数 $m,\omega:\mathrm{Fin}\,d\to\mathbb R$，满足每个 $j:\mathrm{Fin}\,d$ 都有 $m_j>0$、$\omega_j>0$。设 $\ell_j=\sqrt{\hbar/(m_j\omega_j)}$，$\mathrm{He}_n$ 表示 probabilists Hermite 多项式。对每个自然多重指标 $\alpha:\mathrm{Fin}\,d\to\mathbb N$ 定义

$$
\Phi_\alpha(x)=\prod_{j:\mathrm{Fin}\,d}
\frac{\mathrm{He}_{\alpha_j}(\sqrt 2\,x_j/\ell_j)
\exp(-(x_j/\ell_j)^2/2)}
{\sqrt{\ell_j}\sqrt{\alpha_j!\sqrt\pi}}
\quad\in\mathbb R\subseteq\mathbb C.
$$

则对所有 $\alpha,\beta:\mathrm{Fin}\,d\to\mathbb N$，实际复积分满足

$$
\int_{E_d}\Phi_\alpha(x)\Phi_\beta(x)\,dx
=\begin{cases}1,&\alpha=\beta,\\0,&\alpha\ne\beta.\end{cases}
$$

当 $d=0$ 时，两多重指标均为唯一的空函数，$\Phi_\alpha=1$，上述实际体积为 Dirac 测度，积分等于 $1$。


## Receiving construction and boundary

The receiving proof establishes Gaussian-polynomial integrability and iterated
Hermite lowering, then uses weighted integration by parts to obtain factorial
weighted orthogonality for arbitrary one-dimensional indices. It normalizes and
rescales each coordinate by its positive physical length. The finite product
integral and the actual measure-preserving Euclidean coordinate equivalence
supply the displayed all-dimension integral.

Each factor is a real number embedded in Complex. Thus conjugating the first
factor gives the same integral; this correspondence is used directly inside
consumers and adds no separate normalization or conjugation theorem.

Receiving source:
[PhysicalProductOrthonormality.lean](../../D5/S3/Quantum/Analysis/Hermite/PhysicalProductOrthonormality.lean),
`D5.S3.Quantum.Analysis.Hermite.PhysicalProductOrthonormality.physical_product_orthonormal_integral`.

This conclusion supplies the physical integral pairing. Hilbert-basis assembly,
Hamiltonian action, maximal domains, operator cores, tensor-operator domains,
metaplectic transport and heat or Gibbs statements require their own results.

At a future Mathlib pin, retire the port when a direct application proves this
same displayed-function, all-dimension, all-positive-parameter statement and its
actual consumers validate after the port is removed.
## Verified locator

The immutable donor source is
https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd.
The authenticated source paths at this revision are
`TauCeti/RingTheory/Polynomial/Hermite/Derivative.lean`,
`TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean`, and
`TauCeti/Analysis/SpecialFunctions/Hermite/Function/Orthonormal.lean`.
This locator identifies the Hermite lowering and weighted integration-by-parts
argument. The positive physical rescalings and Euclidean product-volume
transport for the displayed functions belong to the receiving construction.
