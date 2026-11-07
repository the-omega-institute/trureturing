---
bibkey: aivazidis2023commontransversal
authors: S. Aivazidis; M. Loukaki; T. W. Müller
year: 2023
title: On the common transversal probability in finite groups
doi: 10.48550/arXiv.2209.00986
url: https://arxiv.org/abs/2209.00986v2
claim: Problems 5.2 and 5.6 ask about normal-extension monotonicity and uniqueness of finite factorial-weight products.
strata_touched:
  - D5/S3/FiniteGroups/TransversalProbabilityMonotone
  - D5/S3/FiniteGroups/FactorialProductNonunique
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2209.00986

Source: https://arxiv.org/abs/2209.00986v2

# Common transversal probability and normal extensions

The source is arXiv:2209.00986v2. Its Definition 3.1, printed p. 8, states:

> We denote by $\mathrm{DT}_G(H, K)$ the set of all left transversals for $H$ in $G$, which are also right transversals for $K$ in $G$.

> We let $P_G(H,K) \coloneqq \frac{\vert \mathrm{DT}_G(H, K)\vert}{\vert H\vert^n},$ so that $P_G(H, K)$ is the (Laplacian) probability that a left transversal for $H$ in $G$ is also a right transversal for $K$ in $G$.

> If $H = K$, we let $P_G(H) \coloneqq P_G(H, H)$ be the probability that a left transversal for $H$ in $G$ is a two-sided one.

Here $(G:H)=n=(G:K)$. The numerator counts subsets, rather than ordered lists of representatives. The Lean definitions use `Subgroup.IsComplement` for unique multiplication factorizations and rational cardinality division with denominator `Nat.card H ^ H.index`.

Problem 5.2, printed p. 37, asks:

> Suppose that $H \leq G$ and $N \unlhd G$, where $G$ is finite. Is it then always true that $P_G(H) \leq P_G(HN)$ (GAP computations confirm this up to $\vert G\vert = 200$)?

The same problem mentions the homomorphism consequence obtained by combining this inequality with Theorem 3.15, and asks about equality. The delivered result proves the universal normal-extension inequality. It does not assert an equality classification or a separate homomorphism theorem.

Proposition 3.2 supplies the literature counting formula: a double-coset component with t left cosets contributes the probability factor t!/t^t. The formal proof connects this formula to the literal transversal subsets, then compares components under the normal extension.

The published journal version is *On the common transversal probability*, Journal of Group Theory 27(6) (2024), 1233–1285, DOI 10.1515/jgth-2024-0030. [The journal text](https://d-nb.info/1346963460/34) retains Problem 5.6 on printed p. 1281. Completeness of any literature screen remains ASSUMED-UNVERIFIED; source retention does not establish worldwide priority.

## Factorial-product uniqueness

Problem 5.6, arXiv v2 printed p. 37 and journal printed p. 1281, asks whether, for distinct integers greater than one,

$$\prod_{i=1}^n f(t_i)=\prod_{j=1}^k f(s_j),\qquad f(x)=\frac{\Gamma(x+1)}{x^x},$$

forces the same lengths and parameters up to reordering:

> Can we then conclude that n=k and t_i=s_i for all i after rearranging appropriately?

The arXiv version places “distinct” in parentheses; the journal states it without parentheses. For positive integer m the factor is m!/m^m. There is no group-realizability assumption, cardinality bound, fixed sum or prime restriction in this question. Theorem 4.6 treats prime parameters and is a separate statement.

The exact counterexample in `D5/S3/FiniteGroups/FactorialProductNonunique.result` uses two disjoint eighteen-element sets, so it also satisfies the interpretation requiring all parameters across both sides to be distinct. [The dossier](../../Problems/alm2024-factorial-product-uniqueness.md) gives the sets, precise scope and literature limits.

## Finite computation

The independent experiment is in `the-omega-institute/trureturing-experiments`, commit `5a8e6d2c3e02bc26aa92fc574cd5ce8e41f33add`. Its command is `python3 docs/reports/transversal-probability-monotone/check.py`; the program's SHA256 is `efc01c97561032276c7ec83a5e154be5ab3e7c316760b87926fb11b88e5277c4`. Issue #22474 reports exit 0 and `ALL_CHECKS_OK`: 28 groups, 1,807 subgroup/normal pairs and 693 strict comparisons. Its equality criterion is checked only on those finite tables; it is not a uniform equality theorem. These are the preregistration's reported computations, not a fresh execution here.
