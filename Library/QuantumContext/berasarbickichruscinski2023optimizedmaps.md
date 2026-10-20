---
bibkey: berasarbickichruscinski2023optimizedmaps
authors: A. Bera; G. Sarbicki; D. Chruściński
year: 2023
title: Optimizing positive maps in the matrix algebra M_n
doi: 10.48550/arXiv.2309.09621
url: https://arxiv.org/abs/2309.09621v1
claim: "Conjecture 2, Eq. (13), gives the greatest positivity parameter n − k + (n−3)/(n − (2/3)k) at equal coefficient norms when GCD(n,k) = 3."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps
license: citation-only
triage: anchor
---

# Optimization of positive maps

A. Bera, G. Sarbicki and D. Chruściński,
*Optimizing positive maps in the matrix algebra M_n*, arXiv:2309.09621v1.
Page numbers refer to this version.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2309.09621

Source: https://arxiv.org/abs/2309.09621v1

## Source statements

Page 1, Eq. (3):

> τ_{n,k}(X) = (n − k)ε(X) + Σ_{i=1}^{k} ε(Sⁱ X S^{†i}) − X

Page 2, Eqs. (4)–(6):

> ε(X) = Σ_{i=0}^{n−1} Tr[X eᵢᵢ] eᵢᵢ.

> S eᵢ = eᵢ₊₁ (mod n)

> H_{|v⟩}(X) = P_{|v⟩} ∘ X

> P_{|v⟩} = |v⟩⟨v|

The symbol ∘ is the Hadamard product.

Page 2:

> Let λ^max_{|v⟩} be the largest value of λ_{|v⟩}, such that the map τ_{n,k} − λ_{|v⟩} H_{|v⟩} is positive.

Page 3, Eqs. (10)–(11):

> |v₁⟩ = (1/√n)(1, ω^{n/3}, (ω^{n/3})² …, (ω^{n/3})^{n−1})ᵀ

> |v₂⟩ = (1/√n)(1, ω^{2n/3}, (ω^{2n/3})² …, (ω^{2n/3})^{n−1})ᵀ

Here ω = e^{2πi/n}.

Page 3:

> Conjecture 2. If GCD(n, k) = 3, then for the optimized map τ^{λ,α,β}_{n,k} = τ_{n,k} − λ_{|v⟩} H_{|v⟩} where |v⟩ = α|v₁⟩ + β|v₂⟩ one has λ^max_{|v⟩} ∈ [n − k, n − k + (n−3)/(n − ⅔k)]. Moreover, λ^max_{|v⟩} = n − k if α = 0 or β = 0, (12) λ^max_{|v⟩} = n − k + (n−3)/(n − ⅔k) if |α| = |β|. (13)

## Scope

The formal refutation concerns only Eq. (13). At n = 6, k = 3,
α = β = 1/√2, the claimed parameter 15/4 fails positivity on the
positive semidefinite matrix I/60 + (27/60)qq*, q = (1,0,0,1,0,0).
The quadratic form of the output at q is −13/40.
The exact greatest parameter, Eq. (12), the interval assertion and
the general compression family are outside this result.

## Literature boundary

The preregistration #19282 records a partial literature inventory.
Completeness is ASSUMED-UNVERIFIED; the kernel proof establishes the
negation of the stated universal assertion independently of that inventory.
