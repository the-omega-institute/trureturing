---
bibkey: mahalingampandoh2021scatteredpalindromes
authors: K. Mahalingam, P. Pandoh
year: 2021
title: Counting scattered palindromes in a finite word
doi: null
url: https://arxiv.org/abs/2108.02729v1
claim: 'Conjecture 5.6 proposes the sharp maximum of distinct nonempty scattered palindromic subwords and the alphabet sizes at which it is attained.'
strata_touched:
  - D5/S1/Words/Palindromes/ScatteredPalindromeMatching
  - D5/S1/Words/Palindromes/ScatteredPalindromeMaximum
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2108.02729v1

## Scattered subwords and counting

Section 2, page 2: “A word $u$ is a scattered subword of a word $w$, denoted by $u\prec w$, if there exist words $\alpha_1,\ldots,\alpha_n$ and $\beta_0,\ldots,\beta_n$, some of them possibly empty, such that $u=\alpha_1\cdots\alpha_n$ and $w=\beta_0\alpha_1\beta_1\cdots\alpha_n\beta_n$.”

“We denote by $\mathrm{PAL}(w)$ and $\mathrm{SPAL}(w)$, the set of all non-empty palindromic factors, and scattered palindromic subwords of $w$, respectively.” “Also, $P(w)=|\mathrm{PAL}(w)|$ and $SP(w)=|\mathrm{SPAL}(w)|$.” “$Alph(w)$ denotes the set of all the subwords of $w$ of length $1$.”

Page 3: “Throughout the paper, by the number of palindromic factors (resp. scattered palindromic subwords), we mean the number of non-empty distinct palindromic factors (resp. scattered palindromic subwords) in a word.”

`List.Sublist` encodes scattered containment. `spal` filters `w.sublists.toFinset` for nonempty words fixed by reversal; `sp` is its cardinality. `alphabetSize` is `w.toFinset.card`. Thus different embeddings of the same word contribute only once. Example 2.1 lists four subwords of `aabb` but prints a count of five; the listed set has cardinality four. The definitions and conjecture use distinct nonempty words.

## Theorem 5.4

Page 15: “Let $SP^{n,q}=\max\{SP(w)\mid w\in\Sigma^n\text{ and }|Alph(w)|=q\}$, then $SP^{n,q}=2^{n-q}(2q-n+2)-2$ for $q\geq\frac n2$.”

This is the source's established result for alphabet size at least half the length. The general sharp maximum below is a separate statement. The full fixed-alphabet formula is not a public theorem in these modules.

## Conjecture 5.6

Page 18: “The maximum number of scattered palindromic subwords in a word of length $n$ is”

$$
\begin{cases}
3(2^{\lceil n/2\rceil-1})-2,&\text{if }n\text{ is odd},\\
2^{n/2+1}-2,&\text{if }n\text{ is even}.
\end{cases}
$$

“and this bound is achieved only when”

$$
q=\begin{cases}
\lceil n/2\rceil,&\text{if }n\text{ is odd},\\
\frac n2\text{ and }\frac n2+1,&\text{if }n\text{ is even}.
\end{cases}
$$

The encoding uses natural integer division, with `(n + 1) / 2` representing the ceiling. The claim has three clauses: a bound for every word over every decidable alphabet; attainment at every permitted alphabet size for every positive length, using natural-number letters; and necessity of the permitted alphabet sizes for an extremal nonempty word. The bound also covers the empty word.

## Mathematical scope

The proof partitions palindromes by their outer letter and uses a convex inequality for disjoint first-last endpoint pairs. Strong induction gives the bound; equality in the residue budget forces a residual length at most two and the permitted alphabet sizes. Nested fresh outer pairs around zero, one or two distinct central letters attain the bound. The proof constructs these extremizers without classifying every extremal word. The maximum at an arbitrary fixed alphabet size below half the length remains open here.
