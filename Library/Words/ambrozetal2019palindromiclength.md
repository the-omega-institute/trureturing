---
bibkey: ambrozetal2019palindromiclength
authors: Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová
year: 2019
title: Palindromic length of words and morphisms in class P
doi: 10.1016/j.tcs.2019.02.024
url: https://arxiv.org/abs/1812.00711v2
claim: Section 4 recalls Frid's conjecture on Fibonacci prefixes and the upper bound for their palindromic length.
strata_touched:
  - D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength
license: citation-only
triage: anchor
---

# Palindromic length of words and morphisms in class P

## Verified locator

Theoretical Computer Science 780 (2019), pages 74–83.
DOI: https://doi.org/10.1016/j.tcs.2019.02.024
Preprint version: https://arxiv.org/abs/1812.00711v2

## Cited scope

Section 4 discusses the Fibonacci word and recalls Frid's conjecture from
Numeration 2018. The exact originating statement is Conjecture 2, printed
page 12 of that meeting's book of abstracts:

> For every k ≥ 1, the prefix of the Fibonacci word of length (100)²ᵏ⁻¹101 cannot be decomposed as a concatenation of at most 2k palindromes.

The source upper bound is `2k+1`. Combining that upper bound with the conjectured
lower bound would give equality for this particular family of prefixes; it
would not identify palindromic length for every Fibonacci prefix.

The preprint defines the all-factor maximum verbatim (`pallen_classP.tex:101–105`):

```tex
Formally, defining for a given infinite word $\bu$ the function $\PL{u}:\N\to\N$ by
\[
\PL{u}(n) := \max \{ \pall{w} : \text{$w$ is a factor of length $n$ in \bu} \},
\]
```

With `u=f`, Section 4 gives only the following conditional implication
(`pallen_classP.tex:478–482`), verbatim:

```tex
Should this conjecture be valid,
it would imply that
\[
\limsup_{n\to\infty}\frac{\PL{f}(n)}{\ln n} \geq \frac{1}{3\ln\tau}.
\]
```

Here `τ=φ=(1+√5)/2`. Under the stated Fibonacci-word and numeration convention,
the repository proves the prefix equality `PL(goldenFactor (N(k)) 0) = 2*k+1`
for every `k ≥ 1`, discharging the Frid-family conjecture premise of this
implication. The stronger prefix limsup lower bound is repository-derived,
not stated here by AKMP and not formalised in this delivery. Fibonacci growth
and the limsup step remain outside the delivered formalisation; no Lean
limsup theorem is delivered.
