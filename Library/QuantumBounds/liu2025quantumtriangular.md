---
bibkey: liu2025quantumtriangular
authors: Yupan Liu
year: 2025
title: "Quantum state testing beyond the polarizing regime and quantum triangular discrimination"
doi: 10.48550/arXiv.2303.01952
url: https://arxiv.org/abs/2303.01952v5
claim: "We observe that Theorem 1.4(ii) is not tight. Numerical simulations indicate that the tight bound is QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) for any states ρ₀ and ρ₁."
strata_touched:
  - D5/S3/Divergence/QuantumTriangularJensenShannonRefutation
  - D5/S3/Divergence/QuantumTriangularMetricRefutation
license: citation-only
triage: anchor
---

# Quantum state testing beyond the polarizing regime and quantum triangular discrimination

Yupan Liu, *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*, arXiv:2303.01952v5; published in *Computational Complexity* 34 (2025), article 11.

§1.3, “Improved inequalities on the quantum triangular discrimination”, printed p. 7:

> We observe that Theorem 1.4(ii) is not tight. Numerical simulations indicate that the tight bound is QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) for any states ρ₀ and ρ₁.

Immediately after Theorem 3.4:

> Numerical simulations suggest that the tight bound is QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁), while we only managed to prove a slightly weaker bound ½QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) in Theorem 3.4.

Definition 3.1 (p. 13) reads in part:

> QTD(ρ₀, ρ₁) := ½ Tr[(ρ₀ − ρ₁)(ρ₀ + ρ₁)^{−1/2}(ρ₀ − ρ₁)(ρ₀ + ρ₁)^{−1/2}]

> Furthermore, if ρ₀ + ρ₁ is not full-rank, then the inverse is defined only on its support.

Definition 2.10 (p. 10) reads in part:

> QJS(ρ₀, ρ₁) := S((ρ₀+ρ₁)/2) − (S(ρ₀) + S(ρ₁))/2

> Here, S(ρ) := −Tr(ρ ln ρ) denotes the von Neumann entropy of the quantum state ρ

QJS₂ uses the base-2 logarithm.

Yupan Liu, *Complexity-theoretic perspectives on quantum state testing*, PhD thesis,
Nagoya University, January 2025, Open Problem 8.16, printed p. 180
([author's PDF](https://yupanliu.info/assets/pdf/PhD_thesis.pdf)):

> Second, since the square root of triangular discrimination is a metric [LC86], it raises an interesting question whether a similar property holds in the quantum case:

> Open Problem 8.16. Is it possible to prove that the square root of quantum triangular discrimination, denoted as √QTD, is a distance metric? Specifically, for any quantum states ρ0, ρ1, and ρ2, can it be shown that the following inequality holds: √QTD(ρ0, ρ1) + √QTD(ρ1, ρ2) ≥ √QTD(ρ0, ρ2)?

The same triangle assertion occurs in arXiv v5, §1.3, “Improved inequalities on the
quantum triangular discrimination”, introduced by “numerical simulations also
suggest that the triangle inequality holds for the square root of QTD”.

## Verified locator

Author text: <https://arxiv.org/abs/2303.01952v5>.

- arXiv v5, §1.3, “Improved inequalities on the quantum triangular discrimination”, printed p. 7.
- arXiv v5, paragraph immediately after Theorem 3.4.
- arXiv v5, Definition 3.1 (QTD and the inverse on its support).
- arXiv v5, Definition 2.10 (QJS and von Neumann entropy).
- PhD thesis, Open Problem 8.16, printed p. 180: https://yupanliu.info/assets/pdf/PhD_thesis.pdf
- DOI: https://doi.org/10.48550/arXiv.2303.01952

