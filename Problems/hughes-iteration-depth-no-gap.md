---
slug: hughes-iteration-depth-no-gap
bibkey: hughes2026a27755
doi: null
url: https://arxiv.org/abs/2608.27755v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Powers/WordPower.wordPower_succ
---

# Hughes iteration-depth no-gap conjecture

## Problem

For a finite alphabet and arbitrary languages `A` and `B`, fix a positive
insertion degree `k` throughout each iteration history. A word has iteration
depth `m` when `m` is the least stage at which the word occurs for some such
degree. Hughes's Section 10 conjecture states that if depth `r` occurs, every
depth from zero through `r` occurs.

This is the arbitrary-language iteration-depth conjecture on page 8. It is
not the finite-language Theorem 8 and not the insertion-degree conjecture in
Section 11.

## Motivation

The frozen word-power recurrence records repeated concatenation of finite
words. Literal insertion is the next operation considered here: it alternates
source and base factors and then repeats that operation at a fixed degree.
The open question asks whether the first-occurrence stages of this richer
hierarchy still form an initial interval.

## Gap

The paper proves the no-gap property for finite languages by maximum word
length, then asks on page 11 whether the finite case implies the arbitrary
case. That maximum-length argument is unavailable for arbitrary languages.

The bounded prior-art inspection found no exact resolution in the searched
repository, pinned Mathlib, or inspected external sources. The older Hughes
and Ito-Sugiura full texts were unavailable, and the 2025 Ibarra-McQuillan
source was available only at abstract level. This is a bounded search result,
not a worldwide absence claim.

## Route

Pad any degree-`j` insertion factorization to a larger degree `K` by appending
empty `(x,y)` factor pairs. This preserves the concatenated base word, source
word, and output. Induction lifts every stage of the fixed-degree iteration
from `j` to `K`.

Suppose a word first occurs at stage `r+1` through degree `k`, and extract the
base predecessor `v` from its final factorization. If `v` occurred at a stage
`s<r` through degree `j`, lift that predecessor occurrence to
`K=max(k,j)`, pad the final degree-`k` insertion to degree `K`, and obtain the
original word at stage `s+1<r+1`, contradicting minimality. Thus `v` first
occurs at `r`. Induction on `r` supplies every smaller attained depth.

## Falsifier

A finite alphabet, arbitrary languages `A,B`, and a word of minimum depth
`r>0` for which no word has minimum depth `r-1` would refute the theorem. A
failure of empty-pair padding to preserve any of the three literal source
conditions would invalidate the proof route. A formalization using a varying
degree within one history, nonempty-factor assumptions, finite languages, or
the Section 11 degree spectrum would not settle this problem.

## Evidence

The primary PDF has SHA-256
`dd840a73b56821f5342811bcae34904356c7aa2553e624e7fea5183843dfa1cf`.
The literal insertion definition is on page 2, minimum depth is on page 7,
the arbitrary-language conjecture is on page 8, and the related open-question
discussion is on page 11.

## Triage

`theorem`. A complete resolution requires a universal proof for finite
alphabets and arbitrary languages, including empty and epsilon-only cases.

## ASSUMED-UNVERIFIED

The unavailable older full texts and abstract-only 2025 source remain outside
the verified literature scope. No claim is made about sources beyond the
bounded search.
