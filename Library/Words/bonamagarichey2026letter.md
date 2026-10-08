---
bibkey: bonamagarichey2026letter
authors: Miklós Bóna, Balázs Maga, Jacob Richey
year: 2026
title: Letter frequency in shifts of finite type with one forbidden word
doi: null
url: https://arxiv.org/abs/2606.06655v2
claim: 'A word $w$ has $\rho^w = 1/2$ if and only if $w$ has balanced borders.'
strata_touched:
  - D5/S1/Words/Forbidden/ForbiddenWordCounting
  - D5/S1/Words/Forbidden/ForbiddenWordGrowth
  - D5/S1/Words/Forbidden/BorderImbalanceExclusion
  - D5/S1/Words/Forbidden/BalancedBordersHalfFrequency
  - D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary
  - D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2606.06655v2

The Crossref title query returns no matching record. The pinned v2 PDF gives Section 2, Definitions 2.1–2.6, pp. 3–4, for avoiding words, letter frequency and borders; Fact 2.9, p. 5, for the generating function; Definition 3.2 and Proposition 3.3, p. 9, for balanced borders and the sufficient half-frequency condition; Theorem 3.5, p. 9, for one-sided border imbalance; and Section 6, Conjecture 6.1, p. 20. The generating-function locator called Fact 2.6 in the preregistration refers to Fact 2.9 in this PDF.

## Definitions

Definition 2.1, p. 3: “For positive integer $n \geq 1$ and any word $w$ of length $k$, denote by $\Omega_n^w$ the set of words of length $n$ with no $w$ factor, i.e.”

$$
\Omega_n^w = \{(\omega_1,\omega_2,\ldots,\omega_n) \in \{0,1\}^n : \text{for all } i\in[n-k+1],\ \omega_{[i,i+k-1]}\ne w\}.
$$

Definition 2.4, pp. 3–4: “For any word $w$ and positive integer $n$, denote by $\rho_n^w$ the frequency of $1$s over all words in $\Omega_n^w$:”

$$
\rho_n^w = \frac{1}{n|\Omega_n^w|}\sum_{\omega\in\Omega_n^w}|\omega|_1
= \frac{1}{n|\Omega_n^w|}\sum_{j=0}^n j|\Omega_{n,j}^w|.
$$

“Set $\rho^w = \lim_{n\to\infty}\rho_n^w \in [0,1]$ if it exists.”

Definition 2.6, p. 4: “Fix two words $v,w$ with $v\in\{0,1\}^k$. Denote by $\mathcal B(v,w)$ the set of borders of $v$ and $w$:”

$$
\mathcal B(v,w)=\{w_{[1,j]}:j\in\{1,2,\ldots,|w|\},\ w_{[1,j]}=v_{[k-j+1,k]}\}.
$$

Definition 3.2, p. 9: “A word $w$ has balanced borders if for all $b\in\mathcal B(w,w)$, $|b|=2|b|_1$.”

## Conjecture

Conjecture 6.1, p. 20: “A word $w$ has $\rho^w = 1/2$ if and only if $w$ has balanced borders. The same holds with $\rho^w$ replaced by $q^w$.”

The Lean claim encodes only the first sentence, for every nonempty `List Bool` word, with `true` representing 1 and `List.IsInfix` representing factor containment. It reads the equality of the limiting frequency as convergence of the source averages to $1/2$. Borders are nonempty prefixes that are also suffixes; the whole word is included. No unconditional limit-existence hypothesis is added. The source asserts unconditional existence; its formal proof is outside this claim. The $q$ clause remains outside the settlement.
