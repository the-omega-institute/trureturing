---
bibkey: gahramanovmammadov2026pais
authors: Ilmar Gahramanov and Gulmammad Mammadov
year: 2026
title: Polynomial integrals and Poisson structures of the Pais-Uhlenbeck oscillator
doi: null
url: https://arxiv.org/abs/2611.17457v1
claim: The full real resonant coordinate algebra has the defining relation and two signed Poisson brackets of (16), (21), (23), (26) and (27). Section 5.3 proves diagonal rescaling equivalence when either resonance exponent is even and asks about nonlinear isomorphisms when both are odd.
strata_touched:
  - D5/S3/Geometry/Poisson/PaisPoissonNonisomorphism
license: citation-only
triage: anchor
---

# Polynomial integrals and Poisson structures of the Pais-Uhlenbeck oscillator

## Verified locator

https://arxiv.org/abs/2611.17457v1

arXiv:2611.17457v1 [math-ph], 12 November 2026.
Primary PDF, Section 5.3, page 5, after (29), available at
https://arxiv.org/pdf/2611.17457v1#page=5.

> For m and n both odd no such rescaling exists, and we leave open whether the two algebras are isomorphic by a nonlinear change of generators.

Equations (16) and (21) present the defining relation. Write u=H₁, v=H₂, x=X and y=Y. The full real coordinate algebra is ℝ[u,v,x,y]/(x²+y²−uⁿvᵐ). The source uses the rational frequency ratio m:n in lowest terms and Ω=nω₁=mω₂.

| Ordered generator pair | Canonical (23) | Alternative (26), (27) |
| --- | --- | --- |
| u,v | 0 | 0 |
| u,x | Ωy | Ωy |
| v,x | Ωy | −Ωy |
| u,y | −Ωx | −Ωx |
| v,y | −Ωx | Ωx |
| x,y | −(Ω/2)uⁿ⁻¹vᵐ⁻¹(nv+mu) | −(Ω/2)uⁿ⁻¹vᵐ⁻¹(nv−mu) |

The signs are consistent with X±=X±iY and {X+,X−}=−2i{x,y}.
Section 5.3 separates abstract polynomial Poisson-algebra isomorphism
from the physical invariant image (30), where both sector energies are
nonnegative. The diagonal rescalings (28) and (29) exclude the odd pair
only within that family. The source leaves nonlinear changes of generators
open in its stated scope.

The repository derivation uses the full real algebra and all unital real
characters, including characters with negative sector values. This distinction
is material to the character-fiber obstruction. The recorded public proof is
https://github.com/the-omega-institute/trureturing/issues/34936#issuecomment-7226713190.
It establishes nonisomorphism for any odd positive natural n,m and any
nonzero real Ω. The result specializes to the coprime ordered positive-frequency
parameters in the paper. This extension is a repository-derived result; the
paper is evidence for the question and definitions.

The primary version was read directly in the independent replay, with PDF SHA-256
813c2aae2a5c33eeb352a53d1990d28abddba7745adb4393b905453a957ce53b.
The registered statement is at
https://github.com/the-omega-institute/trureturing/issues/34936#issuecomment-7225843074.
