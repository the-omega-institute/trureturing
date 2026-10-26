---
bibkey: faust2026spectralinvariants
authors: M. Faust, L. Friedman, G. O'Malley, R. Ramos and A. Sharma
year: 2026
title: Algebraic Properties of the Ideal of Spectral Invariants for the Discrete Laplacian
doi: 10.48550/arXiv.2602.08304
url: https://arxiv.org/abs/2602.08304v1
claim: "Conjecture 3 asserts that V(I') has only regular nonzero points for odd periods."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/FaustSpectralInvariantsOddRefutation
license: citation-only
triage: anchor
---

# Spectral-invariant ideal and odd-period regularity

## Verified locator

DOI: 10.48550/arXiv.2602.08304

Source: https://arxiv.org/abs/2602.08304v1

Section 2, p. 3: “Thus, from here on we write L_V in place of L_V(1)”.
“Let D_V(λ) denote the characteristic polynomial of L_V”. Its sign is
fixed by det(L_V−λI), and ζ_V := D_V(λ)−D_𝟎(λ).
Section 4, p. 8: “For odd n= 2m+1, this yields a potential function of the form
(u₁, …, uₘ, 0, −uₘ, …, −u₁).” Page 9 defines
p′ₖ := (−1)ⁿ⁺ᵏ ζ_U[λⁿ⁻²ᵏ], I′ := ⟨p′₁, …, p′ₘ⟩.

Conjecture 3, p. 11, states: “When q is odd, then V(I′) has only regular
nonzero points, and when it is an even number greater than 6 there is
a single singular point, up to symmetry, of multiplicity 2^{q/2−2}.
Moreover, the multiplicity at 𝟎 is 2^{⌊q/2⌋}.”

Section 3, p. 7: “we are always referring to the multiplicity of a point according
to the defining ideal (not with respect to the radical).”

The source uses periods, without requiring least period. The Lean
refutation uses the preregistered Jacobian determinant criterion for
regularity, with no separate local-algebra multiplicity theorem.
The witness has period five repeated three times at q=15.
Literature completeness is ASSUMED-UNVERIFIED; no prior settlement
was found in the bounded search recorded in issue #19188.
