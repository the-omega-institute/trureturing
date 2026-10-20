---
bibkey: svinin2015discrete
authors: A. K. Svinin
year: 2015
title: On integrals for some class of ordinary difference equations admitting a Lax pair representation
doi: 10.1088/1751-8113/49/9/095201
url: https://arxiv.org/abs/1505.06394v2
claim: Conjecture 1 asserts the discrete-polynomial convolution identity (48) in every degree for the case (h,n)=(1,1).
strata_touched:
  - D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity
license: citation-only
triage: anchor
---

# Svinin's discrete-polynomial identity

## Verified locator

DOI: 10.1088/1751-8113/49/9/095201

Source: https://arxiv.org/abs/1505.06394v2

The version is arXiv v2 (17 September 2015), published in *Journal of Physics A:
Mathematical and Theoretical* 49 (2016), 095201. Printed page numbers below refer
to the arXiv v2 PDF.

## Source statements

Page 3, Eq. (4):

> T^r_s(i) := Σ_{{λ_j}∈D_{r,s}} T(i + λ_1h)T(i + λ_2h + n) ⋯ T(i + λ_rh + (r − 1)n) with D_{r,s} := {λ_j : 0 ≤ λ_1 < ⋯ < λ_r ≤ s − 1} … we put T^0_s(i) ≡ 1.

Page 5, Section 2.3:

> S^r_s(i) := Σ_{{λ_j}∈B_{r,s}} T(i + λ_1h + (k − 1)n) ⋯ T(i + λ_{r−1}h + n)T(i + λ_rh) … B_{r,s} ≡ {λ_j : 0 ≤ λ_1 ≤ ⋯ ≤ λ_r ≤ s − 1}.

Page 12, Section 3.4:

> ⟨F, G⟩^r_s(i) = Σ_{j=0}^{r} (−1)^j F^{r−j}_{s+j}(i) G^j_{s−r+j}(i + r − j). Remark that in this formula we put F^r_s(i) ≡ 0 for s ≤ 0.

Page 12, Conjecture 1:

> The relations ⟨S, T⟩^r_s(i) = Σ_{j=0}^{r−2} (−1)^j T(i + r − j − 2)T(i + s + j) × S^{r−j−2}_{s+j+2}(i) T^j_{s−r+j}(i + r − j), ∀ s ≥ r − 1 (48) are identities. Unfortunately, by now we can prove this conjecture only for r = 1, 2, 3.

## Mathematical scope

Section 3 specializes to (h,n)=(1,1). The k in the first S offset on page 5 is
read as r, according to the displayed factor pattern and recurrences (10)–(11).
The Lean definitions use finite strictly monotone and monotone maps
`Fin r → Fin s.toNat`. The zero-based factor a has offset a in T and r−1−a
in S, both evaluated in the integers. Empty products equal one. Thus degree
zero stays one and positive degrees vanish at nonpositive subscripts. The
right side of (48) is an empty sum when r=1. The theorem quantifies over
commutative rings, without division or nonvanishing assumptions.

The proof uses Pascal partitions, reflection, a corrected-convolution
translation identity, and finite-window locality. It supplies the conjectural
prerequisite for the paper's later difference-equation equivalences and first
integrals in this specialization; it does not separately formalize those
statements or settle general coprime (h,n).

## Literature boundary

The search recorded on issue #19287 inspected arXiv:2106.00539v2,
2307.05866, 2502.06908v1 (Remark 5.12), 2604.13115v1, 2606.24925,
and Bobrova's 2605.29722; Hone–Kouloukas–Quispel (2018),
Hone–Roberts–Vanhaecke (2024), and Flajolet (1980) were also screened.
Usmani (1994) was not read. Completeness and publication priority remain
ASSUMED-UNVERIFIED. The source itself proves only r≤3.
