---
bibkey: mathlib2025hilberttensor
authors: Monica Omar; Floris van Doorn; Rémy Degenne; Mathlib contributors
year: 2025
title: Tensor products of inner product spaces and product-measure L2 APIs
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/TensorProduct.lean
claim: The actual inner-product tensor norm and completion APIs, together with L2 integrability, Fubini, finite measurable exhaustions and pi-system induction, support the standard completed product-L2 identification.
strata_touched:
  - D5/S3/Quantum/Analysis/CompletedProductL2
license: Apache-2.0
triage: anchor
---

# Completed Hilbert tensor and product L2

## Verified locator

The fixed upstream sources are:

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/TensorProduct.lean

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Completion.lean

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L2Space.lean

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Prod.lean

https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean#L359

The local integrable uniqueness step uses
`Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero` at line 359.

The tensor module identifies Monica Omar as its author and supplies the
inner-product tensor structure, `TensorProduct.inner_tmul` and
`TensorProduct.norm_tmul`. The L2 module identifies Rémy Degenne and supplies
`memLp_two_iff_integrable_sq_norm` and `L2.integrable_inner`. The product
integral module identifies Floris van Doorn and supplies `Integrable.mul_prod`
and `integral_prod_mul`. Each source carries the Apache-2.0 license header.
The completion structure and continuous-linear completion extension are
upstream APIs. These component sources do not state the complete product-L2
unitary assembled below; no whole-result supplier or originality claim is
assigned to them.

## Theorem 1 Completed product-L2 unitary

For arbitrary measurable spaces X and Y and arbitrary sigma-finite measures
μ on X and ν on Y, there exists a complex linear isometric equivalence
from the metric completion of the algebraic inner-product tensor
L²(X,μ;ℂ) ⊗[ℂ] L²(Y,ν;ℂ) onto L²(X×Y,μ×ν;ℂ).
For every f in L²(X,μ;ℂ) and g in L²(Y,ν;ℂ), this equivalence sends the
completion image of f ⊗ g to the almost-everywhere class of
(x,y) ↦ f(x)g(y). No topology, basis, caller-supplied density, finite
total measure, positive measure or nonempty-space assumption is required.

## Standard product-L2 construction

Let μ and ν be arbitrary sigma-finite measures on measurable spaces X and Y.
Write Hμ = L²(X,μ;ℂ), Hν = L²(Y,ν;ℂ), and Hμν = L²(X×Y,μ×ν;ℂ).
The tensor is the metric completion of the algebraic complex tensor equipped
with its inner-product tensor norm.

For f in Hμ and g in Hν, multiplication of AE representatives defines
p(f,g)(x,y)=f(x)g(y). The squared absolute value is the product of the two
integrable squared norms, so Fubini proves square integrability. Projection
pullbacks of factor null sets prove independence of representatives and the
two complex linearity laws. With the inner product conjugate-linear in its
first argument, Fubini also gives

    ⟪p(f,g),p(h,k)⟫ = ⟪f,h⟫ ⟪g,k⟫.

Double algebraic tensor induction applies this identity to all finite sums,
including every cross term. Thus the tensor lift is an isometry. Its
continuous-linear extension to the actual completion remains an isometry.

Its range M is closed because its domain is complete. Suppose u is orthogonal
to M. Products of the indicators of finite measurable A⊆X and B⊆Y are in M,
and orthogonality gives the vanishing integral of u over A×B. Choose finite
measurable exhaustive sequences Aₙ and Bₘ. The restriction of u to each
Aₙ×Bₘ is integrable by the finite-measure L2-to-L1 inclusion. Its integral on
an arbitrary measurable rectangle S×T is the integral of u on
(S∩Aₙ)×(T∩Bₘ), hence zero. Rectangles form a pi-system generating the product
sigma-algebra. Complementation and countable disjoint unions preserve the
zero-integral predicate for this integrable restriction, so pi-system
induction gives zero integral on every measurable set. Uniqueness from set
integrals gives zero AE on the restriction. Taking the countable intersection
of these AE conclusions and using the exhaustive covers gives u=0.
Orthogonal projection onto the closed range therefore proves surjectivity.

The resulting completed unitary has the AE product law for every pair f,g.
No factor is required to have finite measure, finite Hilbert dimension, a
chosen basis, or positive coordinate dimension.

## Physical coordinate and empty-factor applications

Finite Euclidean coordinate spaces are transported through the measurable
`WithLp` equivalences, product-coordinate splitting and coordinate
reindexing. Their volume-preserving laws use actual Euclidean volume and
product measures. Pullback and inverse pullback give the exact physical L2
identification for k and n−k coordinates, including k=0, k=n and n=0.
An empty coordinate type gives a singleton Euclidean space. Its volume is
Dirac mass one at zero and its L2 is the one-dimensional scalar Hilbert
space, via constant representatives; it is not the zero space.

This construction is the function-space tensor bridge. It does not identify
oscillator domains or prove metaplectic covariance, Hamiltonian equality,
selfadjointness, trace class, a Gibbs state factorization, or a partition
identity. Those statements require their own operator and domain joins on
the same physical Hilbert spaces.
