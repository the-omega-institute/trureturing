---
bibkey: dlmfcomplexpowerhyperbolic
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: Logarithms, Powers, and Hyperbolic Functions
doi: null
url: https://dlmf.nist.gov/4.2
claim: A selected logarithm defines a complex power; hyperbolic sine and cosine are exponential difference and sum.
strata_touched: []
license: citation-only
triage: anchor
---

# Logarithms, powers, and hyperbolic functions

The primary definitions are [DLMF §4.2(i)](https://dlmf.nist.gov/4.2.i),
[§4.2(iv), equation 4.2.28](https://dlmf.nist.gov/4.2.E28), and
[§4.28, equations 4.28.1–3](https://dlmf.nist.gov/4.28).

For a selected logarithm value $L$ of a nonzero complex number $z$, the
corresponding power is $e^{tL}$. DLMF's principal power uses the principal
logarithm and is analytic off the negative real cut; the two boundary values
on that cut must be distinguished. In particular, for
$\psi=-\varphi^{-1}$ and $a=\log\varphi$, the lower and upper values are
$-a-i\pi$ and $-a+i\pi$. They give conjugate powers when $t$ is real,
and equal powers when $t$ is an integer. These conclusions do not give
pointwise conjugacy for nonreal $t$.

The hyperbolic definitions consumed by the theory volume are

```math
\sinh z=\frac{e^z-e^{-z}}2,\qquad
\cosh z=\frac{e^z+e^{-z}}2,\qquad
\cosh z\pm\sinh z=e^{\pm z}.
```

The consumer is
[FIB hyperbolic geometry and phase boundary, §§一–三](../../docs/develop/theory/AURIC_FIB_HYPERBOLIC_GEOMETRY_AND_PHASE_BOUNDARY.md).
The selected branch, matrix realization and five-mode source-law bridge
are supplied by that consumer's definitions and proofs; DLMF supplies
the scalar definitions, not a native fractional tree operation or a
physical interpretation.
