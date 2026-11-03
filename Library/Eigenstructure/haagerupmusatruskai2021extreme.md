---
bibkey: haagerupmusatruskai2021extreme
authors: Uffe Haagerup; Magdalena Musat; Mary Beth Ruskai
year: 2021
title: "Extreme Points and Factorizability for New Classes of Unital Quantum Channels"
doi: 10.1007/s00023-021-01071-y
url: https://arxiv.org/abs/2006.03414v4
claim: "The paper introduces a two-parameter family of unital, trace-preserving completely positive maps on 3 by 3 matrices with four Kraus operators. Almost every member is factorizable and extreme among the unital trace-preserving completely positive maps, but extreme neither among the unital nor among the trace-preserving ones. At alpha = beta = 1/sqrt(2) the channel is a convex combination of a unitary conjugation and a Choi-rank-3 map extreme in both larger sets; the paper conjectures the same decomposition whenever |alpha| = |beta| = 1/sqrt(2)."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition
license: citation-only
triage: anchor
---

# Haagerup, Musat and Ruskai, Extreme points and factorizability for new classes of unital quantum channels

U. Haagerup, M. Musat and M. B. Ruskai, arXiv:2006.03414v4 [math.OA]; Annales Henri Poincaré 22(10) (2021), 3455–3496. Quotations are from the v4 TeX source, with the source's macros `\1rt2`, `\kb`, `\proj`, `\ovb`, `\half` and `\ds` expanded.

Theorem `thm:UCPT`, with its displayed `align` of the four operators set inline:

> Let $\alpha, \beta \in {\bf C}$ with $ | \alpha |^2 + | \beta|^2 = 1 $ and let
> $A_1 = \alpha |e_1\rangle\langle e_1| + |e_2 \rangle\langle e_3 |$, $A_2 = \beta |e_1 \rangle\langle e_3 | + |e_3 \rangle\langle e_2 |$, $A_3 = - |e_1 \rangle\langle e_2 | - \overline{\beta} | e_3 \rangle\langle e_1 |$, $A_4 = |e_2 \rangle\langle e_1 | + \overline{\alpha} |e_3\rangle\langle e_3|$.
> Then $\Phi_{\alpha,\beta}(\rho) = \tfrac12 \sum_{k = 1}^4 A_k^* \rho A_k$ is an extreme point in the set of UCPT maps if $|\alpha|^2 \neq 0, \tfrac12, 1$. Moreover, $\Phi_{\alpha,\beta}$ has an exact factorization through $M_3({\bf C}) \otimes M_2({\bf C})$ for all $\alpha, \beta$.

In the subsubsection "Non-extreme cases", the source mixes the Kraus operators at $\alpha=\beta=\tfrac1{\sqrt2}$ by $W=2|\mathbb 1_4\rangle\langle\mathbb 1_4|-I_4$. This gives $\Phi=\tfrac14\tilde X_2^*\rho\tilde X_2+\tfrac34\Psi(\rho)$ with $\tilde X_2$ unitary and $\Psi$ extreme in both the UCP and the CPT maps, of Choi rank 3. It then states:

> The argument above easily extends to $\alpha = \pm \overline{\beta}$ with $2 X_3$ unitary. It seems reasonable to conjecture that, whenever $|\alpha | = |\beta| = \tfrac{1}{\sqrt{2}}$, the channel $\Phi_{\alpha,\beta} $ is a convex combination of a unitary conjugation and a map with Choi-rank $3$ which is extreme in both the UCP and CPT maps. However, one would need a different unitary transformation relating $\{ A_k \} $ to $\{ X_k \} $.

## Verified locator

Source: https://arxiv.org/abs/2006.03414v4
- DOI: https://doi.org/10.1007/s00023-021-01071-y (Annales Henri Poincaré 22(10), 3455–3496; published online 12 June 2021; title, authors, journal, volume, issue and pages from Crossref).
- URL: https://arxiv.org/abs/2006.03414v4. The e-print is a single gzipped file `HMR2021J.tex` (2221 lines, md5 `1162bc95019201f2037c415c7b1cf7aa`). Locations:
  - macro `\tfrac{1}{\sqrt{2}}`, l. 56;
  - Subsection `sect:UCPT`, l. 274; Theorem `thm:UCPT`, l. 280–290;
  - Subsubsection "Non-extreme cases", l. 354; the base case at $\alpha=\beta=\tfrac1{\sqrt2}$, l. 366–384; the conjecture, l. 386–392.
- The arXiv record lists versions v1 (5 June 2020) to v4 (19 May 2021) (arXiv API metadata).
