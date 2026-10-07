---
bibkey: maitykrishna2025mutuallyabelian
authors: Anuran Maity, K. V. Krishna
year: 2025
title: "Mutually Abelian-Bordered Binary Words"
doi: 10.1007/978-3-032-17801-5_6
url: https://arxiv.org/abs/2509.20773v1
claim: "Do the limits $\lim_{n\to\infty} \mathcal{M}(n)/2^{2n}$ and $\lim_{n\to\infty} \overline{\mathcal{M}}(n)/2^{2n}$ exist?"
strata_touched:
  - D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/978-3-032-17801-5_6

URL: https://arxiv.org/abs/2509.20773v1

Source: arXiv v1, Section 5 (Conclusion), question 1, p. 29. The published chapter is in SOFSEM 2026, LNCS 16448, pp. 75–89.

## Question

“Do the limits $\lim_{n\to\infty} \mathcal{M}(n)/2^{2n}$ and $\lim_{n\to\infty} \overline{\mathcal{M}}(n)/2^{2n}$ exist?”

## Definitions

Section 1, Definition 1.1, p. 2:

“We say a pair of words $(x, y)$ is an internal abelian-border of $(u, v)$ if $x$ is a nonempty proper suffix of $u$ and  $y$ is a proper prefix of $v$ such that $x \sim_{\textup{abl}} y$. Similarly, we say the  pair $(x, y)$ is an external abelian-border of $(u, v)$ if $x$ is a nonempty proper prefix of $u$ and  $y$ is a proper suffix of $v$ such that $x \sim_{\textup{abl}} y$. A pair of words $(u, v)$ is said to be mutually abelian-bordered if $(u, v)$ has both internal abelian-border and external abelian-border.”

Section 1, Definition 1.2, p. 2:

“If a pair of words $(u, v)$ has neither an internal abelian-border nor an external abelian-border, then $(u, v)$ is said to be mutually abelian-unbordered pair of words.”

Section 2, p. 3:

“The number of MAB pairs $(u, v)$ with $|u| = |v| = n$ is denoted by $\mathcal{M}(n)$.”

Section 3, p. 25:

“Let $\overline{\mathcal{M}}(n)$  denote the number of mutually abelian-unbordered pairs of binary words $(u, v)$ where $|u|=|v|=n$.”

Abelian equivalence means equal counts of every letter. The counts use ordered pairs and permit different lengths for the two borders, including overlap. The binary alphabet is encoded by Bool and word positions by Fin n.
