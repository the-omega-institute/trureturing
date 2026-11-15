---
bibkey: banicaoztekepittau2018isolated
title: Isolated partial Hadamard matrices, and related topics
authors: T. Banica; D. Özteke; L. Pittau
year: 2018
doi: 10.1142/S1230161218500099
url: https://arxiv.org/abs/1706.00986v2
claim: "Conjecture 1.14 asserts a positive real density margin forcing isolation of every prime partial Fourier matrix above that density."
strata_touched:
  - D5/S3/Quantum/Tomography/Hadamard/BanicaTruncationRefutation
license: citation-only
triage: anchor
---

# Isolated partial Hadamard matrices, and related topics

## Verified locator

DOI: 10.1142/S1230161218500099.

Source version: https://arxiv.org/abs/1706.00986v2.

These are the supplied bibliographic locators. The source text has not been
independently retrieved in the offline verification scope.

## Statement

Conjecture 1.14 (Truncation):

> There exists a constant ε>0 such that F_{S,p} is isolated, for any p prime, once S ⊂ Z_p satisfies |S| ≥ (1−ε)p.

For a positive integer p and a row set S in Z/pZ, the partial Fourier matrix has
entries exp(2 pi i s j / p). The partial Hadamard condition requires unit complex
norm at every entry and zero inner product between each pair of distinct rows.
The specified isolation predicate quantifies over globally analytic real curves
through the matrix, satisfying that condition on a neighborhood of zero. The
source's trivial curves have entries H[i,j] q^{α[i]+β[j]} for fixed real
exponents. The Lean encoding instead allows arbitrary real row and column phase
functions a[i](t), b[j](t), with entries H[i,j] exp(i (a[i](t)+b[j](t)):
parameterwise diagonal unitary multiplication. This includes the source class,
so source isolation implies encoded isolation, and the encoded refutation
implies that the source conjecture is false. The common phase H exp(i t²) is
trivial in the encoding, by taking a[i](t)=t² and b[j](t)=0. In the pinned
Mathlib, `ContDiff ℝ ⊤` uses the analytic order `ω`; it implies smoothness of
every finite order.

## Fourier incidence mechanism

For a proper row set and a nonzero step a at prime modulus p, the induced step-a
circle is a union of paths. Choosing a missing vertex cuts that circle, and
cumulative sums of edge values give a right inverse of its incidence map.
Applying these inverses at each nonzero Fourier frequency proves surjectivity
of the orthogonality differential. The reverse-pair conjugation condition lets
the real part of a complex Fourier solution realize the prescribed real phase
equations.

For m rows, a surjective differential has real kernel dimension
m p - m(m-1). The row-column phase subspace has dimension m+p-1 for nonempty
row and column sets. At m=p-2 these values are 3(p-2) and 2p-3, leaving p-3
additional directions. At m=p-1 they coincide, leaving no dimensional excess.

The formal refutation constructs a global analytic regular-level-set curve with
a tangent outside the row-column subspace. Triviality would force the phase
exponentials E[s,j](t)=exp(i c[s,j](t)) to satisfy the cross-product identity
E[s,j] E[s₀,j₀] = E[s,j₀] E[s₀,j]. Differentiating this identity at zero gives
vanishing tangent cross-differences. Writing w=κv for the realized tangent,
the parameters A[s]=w[s,j₀]-w[s₀,j₀] and B[j]=w[s₀,j] reconstruct
w[s,j]=A[s]+B[j], contradicting the chosen tangent after division by κ>0.
The arbitrary phase functions a and b are never differentiated. Its closed theorem is
`BanicaTruncationRefutation.result : Not claim`. The formal tangent argument uses
the sufficient bound m+p for row-column phases; the sharp dimension m+p-1 and
the zero excess at p-1 rows are not separate formal theorems here.
