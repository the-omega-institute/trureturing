---
bibkey: kovacevictan2018multisetvolume
authors: M. Kovačević; D. Tan
year: 2018
title: "Codes in the Space of Multisets—Coding for Permutation Channels with Impairments"
doi: null
url: https://arxiv.org/html/1612.08837v5
claim: "Equation (4) defines the multiset distance by the larger signed mass, and Lemma 2, equation (17), gives the exact volume r^m/m! times binomial(2m,m) for the constrained signed body."
strata_touched:
  - D5/S3/Geometry/BooleanRotationCodebook
license: citation-only
triage: anchor
---

# Kovačević–Tan constrained multiset volume

## Verified locator

Source: https://arxiv.org/html/1612.08837v5

The cited source is M. Kovačević and D. Tan, *Codes in the Space of
Multisets—Coding for Permutation Channels with Impairments*, arXiv:1612.08837v5
(21 June 2018). Equation (4) defines the distance as the larger of the positive
and negative masses. Lemma 2, equation (17), states
\[
\operatorname{Vol}(S_m^{\mathrm{con}}(r))
 = \frac{r^m}{m!}\binom{2m}{m}
\]
for integer \(r\) and \(m\ge 1\), with an orthant-product simplex proof.

The repository's `signedBody` is the real-valued Boolean subset-sum analogue of
this constrained signed body. The Lean theorem
`D5/S3/Geometry/BooleanRotationCodebook.signed_body_volume` supplies its own
kernel-checked proof for arbitrary positive real epsilon and also covers the
zero-dimensional case. This note records the source precedent; it does not
attribute the Boolean rotation application or its no-wrap argument to the
paper.
