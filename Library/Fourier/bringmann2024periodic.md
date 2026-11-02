---
bibkey: bringmann2024periodic
authors: "Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane"
year: 2024
title: "Periodic sign changes for weakly holomorphic eta-quotients"
doi: 10.48550/arXiv.2409.07164
url: https://arxiv.org/abs/2409.07164v1
claim: "Appendix A Table 1 asks for the period-nine signs of the normalized Euler quotient with exponents 9 at 1 and -6 at 3."
strata_touched:
  - D5/S3/Arith/ModularForms/CubicThetaLattice
  - D5/S3/Arith/ModularForms/CubicThetaCoreProduct
  - D5/S3/Arith/ModularForms/CubicThetaIdentities
  - D5/S3/Arith/ModularForms/EtaSignK6
license: citation-only
triage: anchor
---

# The exact k6 normalized Euler sign question

## Verified locator

DOI: 10.48550/arXiv.2409.07164

URL: https://arxiv.org/abs/2409.07164v1

The inspected v1 primary TeX is `single-source.tex`, extracted text SHA256
`cf5c92e1e04a9310d3ef71f6bd839274bd2c611240fb26d4ae988098a42717ab`.
The introduction defines the coefficients by normalized Euler products.
Appendix A Table 1, HTML locator `A1.T1.4`, contains the exact entry
`1^9 3^(-6)` with the pattern `+-+--++-+`, starting at residue zero.
The author-hosted manuscript dated May 21, 2025, printed p. 21, repeats
this entry; its PDF SHA256 is
`8e07e6cb135e2bbb3c9caa082ed0262c2aa9b6b1bfccd6f0162cc570191ebace`.
The publisher's typeset table was not inspected.

## Exact scope and formal anchors

Write `E(X)=prod_(j>=1)(1-X^j)`. The question concerns every natural
index of `F6=E(X)^9/E(X^3)^6`, including zero. The coefficient is positive
exactly at residues `0,2,5,6,8` modulo nine and negative exactly at
`1,3,4,7`; there are no zero or exceptional entries in the stated claim.
The eta shift is `-3/8` and the weight is `3/2`. These shifts do not rotate
the residue labels of the normalized Euler coefficients.

The formal anchor
`D5/S3/Arith/ModularForms/CubicThetaLattice.norm_theta_dissection`
is a classical lattice intermediate motivated by this question. It is
not the original sign theorem. The later anchor
`D5/S3/Arith/ModularForms/CubicThetaCoreProduct.coeff_core_product`
identifies the full core lattice coefficients with the actual Euler
quotient `E(X^3)^3/E(X)` for every natural index.

`D5/S3/Arith/ModularForms/CubicThetaIdentities.B_dissection` and
`D5/S3/Arith/ModularForms/CubicThetaIdentities.cubic_identity` prove the
two remaining classical Borwein identities from actual products and
complete lattice sums. They are proved in Lean, not premises of the
sign theorem.

`D5/S3/Arith/ModularForms/EtaSignK6.F6` is the actual normalized quotient:
the ninth power of Mathlib's pentagonal Euler series times the sixth
power of the unit inverse of its expansion by three. Its `C6` is the
coefficient at the original natural index.
`D5/S3/Arith/ModularForms/EtaSignK6.five_coefficient_formulas` gives the
two progressions modulo three and the three remaining progressions
modulo nine, with factors `-9`, `27`, `1`, `-6`, and `9`.
`D5/S3/Arith/ModularForms/EtaSignK6.all_index_signs` proves both exact
modulo-nine sign biconditionals and nonvanishing for every natural
index. Ordinary partition positivity, including the empty partition,
supplies strictness at every index. No separate analytic eta bridge is
needed for these source-defined normalized Euler coefficients.

The supplied bounded literature review found no inspected theorem stating
the complete k6 entry. This note asserts no worldwide absence, priority,
unique status, independent formal acceptance, CI success, or publication
of the original-problem resolution. The separate k10 entry is outside
this formalization scope.

Citation and question boundary only; no source text or PDF is vendored.
