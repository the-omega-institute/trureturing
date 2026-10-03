---
bibkey: zhao2024vincular
authors: William Zhao
year: 2024
title: Stack-sorting with Stacks Avoiding Vincular Patterns
doi: 10.1016/j.disc.2025.114834
url: https://arxiv.org/abs/2410.17057v1
claim: "Conjectures 4.14 and 5.2 on preimage counts of vincular-pattern-avoiding stack-sorting maps, Conjecture 3.30 on the Schröder enumeration of a sorting class, and Conjecture 5.1 on three stacks with equal sorting classes."
strata_touched:
  - D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations
  - D5/S3/Combinatorics/VincularStack/VincularStackSort
  - D5/S3/Combinatorics/VincularStack/VincularStackThree
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

Conjecture 3.30, Section 3.2, printed page 11:

> The sorting class of $SC_{\underline{23}1}$ is enumerated by $|\mathrm{Sort}_n(SC_{\underline{23}1})| = S_{n-1}$.

Here $S_m$ is the large Schröder number (OEIS A006318) and $\mathrm{Sort}_n(SC_\sigma)$ is the set of
permutations of length $n$ that $s\circ SC_\sigma$ maps to the identity, i.e. whose image under $SC_\sigma$
avoids 231. Proposition 3.29 on the same page gives $SC_{\underline{23}1}(25314)=54132$ and
$SC_{\underline{23}1}(2413)=3142$; the right-greedy rule below reproduces both values.

Conjecture 5.1, Section 5, printed page 20:

> The sorting classes of $SC_{312}$ and $SC_{\underline{31}2}$ are identical. That is, $\mathrm{Sort}_n(SC_{312}) = \mathrm{Sort}_n(SC_{\underline{31}2}) = \mathrm{Sort}_n(SC_{3\underline{12}})$. Furthermore, for $\tau \in \mathrm{Sort}_n(SC_{312})$, we have $SC_{312}(\tau) = SC_{\underline{31}2}(\tau) = SC_{3\underline{12}}(\tau)$.

The three classes have sizes 1, 2, 5, 15, 52, 201, 843, 3764, 17659 for n ≤ 9, as in Table 2 of the source.
In the formal statement `Contains312 adj31 adj12` is classical 312 containment, with the entries
playing 3 and 1 required to be adjacent when `adj31` holds and those playing 1 and 2 when `adj12`
holds; all three machines use the same right-greedy rule.

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
- Conjecture 3.30: Section 3.2, printed page 11.
- Conjecture 4.14: Section 4.1.4, printed page 17.
- Conjecture 5.1: Section 5, printed page 20.
- Conjecture 5.2: Section 5, printed page 20.
- Vincular containment: Introduction, printed page 1.
