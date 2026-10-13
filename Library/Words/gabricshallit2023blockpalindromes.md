---
bibkey: gabricshallit2023blockpalindromes
authors: D. Gabrić and J. Shallit
year: 2023
title: "Smallest and Largest Block Palindrome Factorizations"
doi: 10.1007/978-3-031-33180-0_14
url: https://arxiv.org/abs/2302.13147
claim: "Conjecture 5 states that the expected width of the largest block-palindrome factorization tends to 1 plus twice the A274199 generating series. Lemma 3 gives the source's auxiliary tail bound."
strata_touched:
  - D5/S1/Words/BlockPalindromes
license: citation-only
triage: anchor
---

# Gabrić–Shallit 2023 block-palindrome factorizations

The paper studies smallest and largest block-palindrome factorizations. Conjecture 5 concerns the limiting expected width of the largest factorization, and Lemma 3 is the auxiliary estimate used in the paper's original existence argument.

## Verified locator

DOI: 10.1007/978-3-031-33180-0_14

Source: https://arxiv.org/abs/2302.13147

## Source statements

On page 1:

> A border of a word $w$ is a non-empty word that is both a proper prefix and suffix of $w$.

> A word is said to be bordered if it has a border. Otherwise, the word is said to be unbordered.

On page 2, the paper defines the factorization:

> Let $w$ be a non-empty word. A block palindrome factorization (or BP-factorization) of $w$ is a factorization $w=w_m\cdots w_1w_0w_1\cdots w_m$ of a word such that $w_0$ is a possibly empty word, and every other factor $w_i$ is non-empty for all $i$ with $1\leq i\leq m$.

> We say that a BP-factorization $w_m\cdots w_1w_0w_1\cdots w_m$ is of width $t$ where $t=2m+1$ if $w_0$ is non-empty and $t=2m$ otherwise.

> The largest BP-factorization of a word $w$ is a BP-factorization $w=w_m\cdots w_1w_0w_1\cdots w_m$ where $m$ is maximized (i.e., where the width of the BP-factorization is maximized).

On page 5:

> From the definition of expected value, it follows that $E_{n,k}=\frac{1}{k^n}\sum_{i=1}^n i\cdot\mathrm{LBP}_k(n,i)$.

> **Conjecture 5.** Let $k\geq2$. Then
> $$E_k=1+\sum_{i=1}^\infty a_i k^{-i}$$
> where the sequence $(a_n/2)_{n\geq1}$ is A274199 in the On-Line Encyclopedia of Integer Sequences (OEIS).

A274199 has offset zero. The source expansion fixes the positive-index interpretation: its coefficients are twice A274199 at indices $1,2,\ldots$, giving $2,4,6,10,16,\ldots$. The Lean alphabet is `Fin k`, words are lists, and `bs=[w₁,…,wₘ]` with centre `c=w₀`. The empty word is assigned width zero.

## Computed finding

The source's Lemma 3 asserts $\mathrm{LBP}_k(n,t)/k^n\leq k^{1-t/2}$. At $k=2$, $n=11$, $t=9$, its table gives $192/2048=3/32>2^{-7/2}$. This is a computed finding. The formal proof of the expected-width limit uses the exact renewal recursion and avoids Lemma 3.

The experiment entry [check.py](https://github.com/the-omega-institute/trureturing-experiments/blob/717b7c72b6cadd0aea0aabe864e1bbb8f0a2a948/docs/reports/gabric-shallit-2023-block-palindrome-expected-width/check.py), SHA256 `aa1568275b45ad4b600cb7dad0c84a31c0842225ddd6b6b54cebe740b72ccdcb`, was run as `python3 check.py b274190.txt b274199.txt`; the supplied reading is exit 0, `bad= 0`. It checks the greedy widths, source tables, finite renewal counts, A274190/A274199 coefficients and series identities against enumeration or exact arithmetic.
