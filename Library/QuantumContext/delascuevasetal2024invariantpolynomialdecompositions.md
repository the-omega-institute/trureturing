---
bibkey: delascuevasetal2024invariantpolynomialdecompositions
authors: Gemma De las Cuevas; Andreas Klingler; Tim Netzer
year: 2024
title: "Polynomial decompositions with invariance and positivity inspired by tensors"
doi: 10.1016/j.laa.2024.05.025
url: https://arxiv.org/abs/2109.06680v2
claim: "The paper defines invariant decompositions of polynomials over weighted simplicial complexes with group actions, introduces factorizable (Omega,G) structures through a positive equivariant solution of a product system with right-hand side K_alpha^{-1}, uses factorizability as a hypothesis of its rank inequalities, shows that a free vertex action and the double edge with copy-swapping action are factorizable, and asks whether non-factorizable (Omega,G) structures exist."
strata_touched:
  - D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle
license: citation-only
triage: anchor
---

# Polynomial decompositions with invariance and positivity inspired by tensors

G. De las Cuevas, A. Klingler and T. Netzer, arXiv:2109.06680v2; Linear Algebra and its Applications 698 (2024), 537–588. Quotations are from the v2 TeX source; displayed macros are expanded without changing the wording.

Weighted simplicial complexes (Definition `def:wsc`):

> A *weighted simplicial complex* on $[n]$ is a map $\Omega\colon \mathcal{P}_n\to \mathbb{N}$ such that $\Omega(S_1)$ divides $\Omega(S_2)$ whenever $S_1 \subseteq S_2$.

> A set $S \in \mathcal{P}_n$ is called a *simplex* of $\Omega$ if $\Omega(S) \neq 0$. We will always assume that each singleton $\{i\}$ is a simplex, and call the elements $i\in[n]$ the *vertices* of the weighted simplicial complex. We call a maximal simplex (with respect to inclusion) a *facet* of $\Omega.$

> $\widetilde{\mathcal{F}}$ contains each facet $F$ exactly $\Omega(F)$-many times.

A group action on $\Omega$ consists of an action on $[n]$ leaving $\Omega$ invariant and

> An action of $G$ on the set of multifacets $\widetilde{\mathcal{F}}$ such that the canonical collapse map $c\colon{\widetilde{\mathcal{F}}}\to\mathcal{F}$ is $G$-linear.

Factorizability (Definition before Example "Factorizable group actions"):

> We say that $(\Omega,G)$ is *factorizable* if for each finite index set $\mathcal I$ the following system of equations admits a solution with all $C^{[i]}_{\beta} > 0$ and $C_{{}^g \beta}^{[gi]} = C_{\beta}^{[i]}$ for all $i \in [n]$, $\beta \in \mathcal{I}^{\widetilde{\mathcal{F}}_i}$, and $g \in G$:
> $$C_{\alpha_{\vert_0}}^{[0]} \cdot C_{\alpha_{\vert_1}}^{[1]} \cdots C_{\alpha_{\vert_n}}^{[n]} = K_{\alpha}^{-1} \quad \textrm{ for all } \alpha \in \mathcal{I}^{\widetilde{\mathcal{F}}},$$
> where
> $$K_{\alpha} \coloneqq \big\vert \{\gamma \in \mathcal{I}^{\widetilde{\mathcal{F}}}: \exists g_0, \ldots, g_n \in G \textrm{ with } g_i i = i \textrm{ and } \left({}^{g_i}\gamma\right)_{\vert_i}= \alpha_{\vert_i} \mbox{ for all } i\in[n]\}\big\vert.$$

The open question (Question 38, PDF p. 28 of v2):

> In fact, we are not aware of any non-factorizable $(\Omega,G)$ structures, leading to the following open question.

> Are there non-factorizable $(\Omega,G)$ structures?

The conclusion repeats it as one of two "immediate" open questions. Proposition 39(iii) assumes factorizability for $\operatorname{sos-rank}_{(\Omega,G)}\le\operatorname{sep-rank}_{(\Omega,G)}$; Proposition 39(iv) assumes a free action on a connected $\Omega$ together with factorizability.

## Verified locator

Source: https://arxiv.org/abs/2109.06680v2
- URL: https://arxiv.org/abs/2109.06680v2 (the e-print is a single gzip file whose header names `Manuscript_final.tex`; md5 `e601e0a3202f352cba4bf6d4d13e7db4`, 2167 lines):
  - Definition `def:wsc`, l. 318–341;
  - Definition `def:action` and the group action on a weighted simplicial complex, l. 395–440;
  - Definition (Factorizable), l. 1515–1522;
  - Example (Factorizable group actions), l. 1528–1542;
  - Question `qu:fact`, l. 1544–1549;
  - Proposition `pro:inequalitites`, l. 1553–1566;
  - the conclusion's restatement, l. 2034–2035.
- DOI: 10.1016/j.laa.2024.05.025 (https://doi.org/10.1016/j.laa.2024.05.025; Crossref lists Linear Algebra and its Applications, volume 698, pages 537–588, October 2024).
