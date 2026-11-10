---
bibkey: ambrozetal2019palindromiclength
authors: Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová
year: 2019
title: Palindromic length of words and morphisms in class P
doi: 10.1016/j.tcs.2019.02.024
url: https://arxiv.org/abs/1812.00711v2
claim: Section 4 recalls Frid's Fibonacci prefix conjecture; Section 6 defines mixed pal-antipal length, suggests the sharp factor-two comparison for Thue-Morse prefixes in Table 1, and conjectures unbounded equal-cost prefixes in Table 2.
strata_touched:
  - D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength
  - D5/S1/Words/Palindromes/ThueMorseSignedCut
  - D5/S1/Words/Palindromes/ThueMorseSharpPrefix
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

## Mixed palindrome and antipalindrome scope

Section 6, `pallen_classP.tex` lines 624–635, defines an antipalindrome by
$w=E(w_n)E(w_{n-1})\cdots E(w_1)$, with $E(a)=b$ and $E(b)=a$, and considers
the minimum number of consecutive factors each of which is a palindrome or
an antipalindrome. Empty factors can be removed without changing the word.
The Lean alphabet is `a=false`, `b=true`; exchange is `Bool.not`.

The final paragraph, lines 678–679, says:

> On the other hand, we suppose that there exist prefixes of arbitrary palindromic length whose combined pal-antipal length as big as the palindromic one.

The quantified assertion is: for every $K\geq1$ there exists $n\geq1$ with
$C(t[0:n))=PL(t[0:n))\geq K$. Here both costs are minima for the literal
standard Thue-Morse prefix. The source's finite table does not prove this
unbounded assertion. The signed-potential cut inequality and mixed-prefix
lower bound are repository deductions, rather than results quoted from AKMP.
They do not by themselves close the unbounded equality assertion.

## Sharp factor-two prefix scope

Section 6 explicitly introduces its computations as palindromic and combined
pal-antipal lengths of prefixes of the Thue-Morse word. Its final paragraph,
first sentence, says:

> Our computations suggest that including both palindromes and antipalindromes into the factorization of Thue-Morse word, one can reduce the number of factors by half (and not more), see Table 1.

In that prefix context, the quantified reading is that every positive prefix
has ordinary minimum P(n) at most twice its mixed minimum C(n), and equality
P(n)=2C(n)>0 occurs. Table 1 already lists the finite attainer n=2, P=2, C=1.
The universal bound is a computational suggestion, not a numbered theorem;
its quantified reading and source limits are stated in the
[sharp factor-two dossier](../../Problems/ambroz-kadlec-masakova-pelantova-2019-thue-morse-sharp-factor-two-prefix.md).
The subsequent Table 2 assertion concerns unbounded equal costs C=P and is a
distinct event. Neither an unbounded P=2C family nor all shifted factors is
part of the sharp factor-two settlement. These locators refer to the cited
arXiv v2; equivalence with the unread journal body is not asserted.
