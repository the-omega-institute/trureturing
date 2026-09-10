---
bibkey: nist2026asymptotic
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: Asymptotic Expansions
doi: null
url: https://dlmf.nist.gov/5.11
claim: The digamma asymptotic expansion on positive real arguments has a remainder with the sign of the first omitted term, bounded in magnitude by that term; at positive integers this gives the classical corrected harmonic-logarithmic tail estimate.
strata_touched:
  - D5/S3/Arith/GoldenResource/HarmonicGammaTail
license: citation-only
triage: anchor
---

# Positive real digamma remainders

The cited section, equation (5.11.2), expands the psi function as
`ψ(x) ~ log x - 1/(2x) - Σ B_(2k)/(2k*x^(2k))`.
Section (ii), first paragraph, states that on positive real arguments a truncated
remainder is bounded in magnitude by its first omitted term and has the same sign.
After the `-1/(12x²)` term, the first omitted term is positive, `1/(120x⁴)`.

Together with the classical integer identity `ψ(N) = H_N - γ - 1/N`, this yields
`1/(2N) - 1/(12N²) < H_N - log N - γ` for positive integers. The Lean module gives
an elementary proof using a rational derivative and a monotone corrected sequence.
It formalizes only this lower inequality, followed by a numerical corollary at 128.
The source is not asserted to publish that particular numerical specialization.

Retrieved on 2026-09-10. The source footer reports version 1.2.7, released 2026-06-15.
Equation and sign statement were read directly from the cited page. No mathematical
novelty is claimed for the estimate or its numerical consequence.
