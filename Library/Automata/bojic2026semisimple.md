---
bibkey: bojic2026semisimple
authors: Ana Bojić
year: 2026
title: "Semisimple–Unipotent Decomposition and the Exact Order of a Linear Cellular Automaton over F2"
doi: 10.48550/arXiv.2611.33216
url: https://arxiv.org/abs/2611.33216v1
claim: "Section 2.3 leaves open whether lcm(m_2, ..., m_r) = q for q = 2^k − 1 in the invertible Rule 150 setting. The m_i are the odd orders of the semisimple parts in the nontrivial primary CRT factors in Theorems 8.8 and 8.19."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150
license: citation-only
triage: anchor
---

# Semisimple–Unipotent Decomposition and the Exact Order of a Linear Cellular Automaton over F₂

## Verified locator

- <https://arxiv.org/abs/2611.33216v1> [nlin.CG], 23 November 2026. The open identity is on p. 5 in
  §2.3, “The Gap Addressed by This Paper,” in the
  [paragraph beginning “Kaneko’s (6) result is, in this respect, an
  elementary special case, obtained without factoring”](https://arxiv.org/html/2611.33216v1#S2.SS3.p2.1).
- <https://doi.org/10.48550/arXiv.2611.33216> resolves to the canonical arXiv record.
- Theorem 4.7 identifies the Rule 150 update with multiplication by
  $G(x)=1+x+x^{n-1}$. Theorem 5.2 gives the condition $3\nmid n$ for
  invertibility. Proposition 8.2 and Theorem 8.4 give the multiplicities and
  the primary CRT factors for $n=2^m q$ with $q$ odd.
- Theorem 8.8 characterizes the semisimple factor by its odd order and
  the accompanying unipotent factor. Theorem 8.19 identifies $m_2,\ldots,m_r$
  as the semisimple orders on the factors other than $x+1$ and gives the
  global order formula using their LCM for $q>1$. Section 9.2 identifies the
  calculation with the order of the residue of $G$ in the field modulo $f_i$.

## Source wording

Section 2.3 reads as follows, with mathematical typography restored from
the text extraction.

> The general order formula developed in this paper (Theorem 8.19, Section 8)
> is stated for all $n$ with $3\nmid n$; whether it reduces to Kaneko’s result
> exactly when $q=2^k-1$ depends on whether the local semisimple orders $m_i$
> satisfy $\operatorname{lcm}(m_2,\ldots,m_r)=q$ for that family—a
> number-theoretic fact that has not been verified in this paper and is not
> claimed here.

The staged theorem proves this local identity for $k\ge1$, $m\ge0$ and
$3\nmid q$. It includes $q=1$ through the empty LCM convention. The paper
treats $q=1$ separately in Theorem 8.19. For $q>1$, substituting the identity
into the paper’s global formula yields $2^m q$.
