---
bibkey: zhao2024vincular
authors: William Zhao
year: 2024
title: Stack-sorting with Stacks Avoiding Vincular Patterns
doi: 10.1016/j.disc.2025.114834
url: https://arxiv.org/abs/2410.17057v1
claim: "Conjectures 4.14 and 5.2 on the maximum and second-largest preimage counts of vincular-pattern-avoiding stack-sorting maps."
strata_touched:
  - D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations
license: citation-only
triage: anchor
---

# Zhao's vincular-stack preimage conjectures

The statements below are those of arXiv:2410.17057v1 (2024-10-19).
The underline marks the entries that must be adjacent. Source macros
`\sc`, `\sy`, and `\un` are expanded as `SC`, `\mathfrak{S}`, and
`\underline` in the quotations.

Conjecture 4.14, Section 4.1.4, printed page 17:

> For $n\ge 2$, it holds that
> $$\max_{\pi\in\mathfrak{S}_n}|SC_{1\underline{23}}^{-1}(\pi)|=\max_{\pi\in\mathfrak{S}_n}|SC_{3\underline{21}}^{-1}(\pi)|=2^{n-2}.$$

Conjecture 5.2, Section 5, printed page 20:

> The second-largest number of preimages under $SC_{1\underline{23}}$ that a permutation in $\mathfrak{S}_n$ can have is $2^{n-3}$, for $n\ge 3$. Furthermore, the number of permutations $\pi\in\mathfrak{S}_n$ satisfying $|SC_{1\underline{23}}^{-1}(\pi)|=2^{n-3}$ is $2n-2$.

The introductory definition on printed page 1 reads:

> When considering whether a permutation $\pi$ contains a vincular pattern $\sigma$, some elements may be required to be adjacent in $\pi$, as indicated by underlined terms in $\sigma$. For instance, the pattern $1423$ contains $1\underline{23}$ and $123$, but avoids $\underline{12}3$ and $\underline{123}$.

The encoding uses one-based entries and reads stack words from top to bottom.
The Bool flag false denotes $1\underline{23}$ and true denotes
$3\underline{21}$. Containment quantifies over the entire stack word.
The right-greedy rule follows the Cerbai–Claesson–Ferrari convention: push
when the proposed stack avoids the pattern; otherwise pop its top and retry.
The paper states right-greedy processing without a formal definition of the
stack rule. Its Figures 1–4 send input 514362 to 463215, 263415, 426315, and
632415 respectively for the displayed patterns, fixing this interpretation.

The formal refutation of Conjecture 4.14 checks 129 distinct preimages of
765432819 at n = 9, exceeding the asserted bound 128. The refutation of
Conjecture 5.2 computes fibres of sizes 5 and 8 at n = 5; these are distinct
values above the asserted second-largest value 4. It refutes the conjunction
through its first clause, without separately refuting the multiplicity clause.

The journal version is *Discrete Mathematics* 349(3), 114834 (2026).
Its body text was not retrieved; whether it retains the quoted conjectures
is ASSUMED-UNVERIFIED. The named statements here are fixed to arXiv v1.

## Verified locator

- URL: https://arxiv.org/abs/2410.17057v1
- PDF: https://arxiv.org/pdf/2410.17057v1
- DOI of the published version: https://doi.org/10.1016/j.disc.2025.114834
- Conjecture 4.14: Section 4.1.4, printed page 17.
- Conjecture 5.2: Section 5, printed page 20.
- Vincular containment: Introduction, printed page 1.
