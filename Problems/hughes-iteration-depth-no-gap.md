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
depth from zero through `r` occurs. The formalization also proves this statement
over arbitrary alphabets, with no finiteness or countability assumption.

This is the arbitrary-language iteration-depth conjecture on page 8. It is
not the finite-language Theorem 8 and not the insertion-degree conjecture in
Section 11.

## Motivation

The frozen word-power recurrence records repeated concatenation of finite
words. Literal insertion is the next operation considered here: it alternates
source and base factors and then repeats that operation at a fixed degree.
The published question asks whether the first-occurrence stages of this richer
hierarchy still form an initial interval.

## Gap

The paper proves the no-gap property for finite languages by maximum word
length, then asks on page 11 whether the finite case implies the arbitrary
case. That maximum-length argument is unavailable for arbitrary languages.

The bounded prior-art inspection found no exact resolution in the searched
repository, pinned Mathlib, or inspected external sources. The 2025
Ibarra–McQuillan accepted manuscript was inspected through its definitions,
15 propositions, seven corollaries and conclusion; its binary-operation
decision, closure and transducer results do not state the repeated
fixed-degree minimum-depth spectrum theorem. The relevant portions of the
2007 and 2023 UCF notes and arXiv:2603.26162v2 likewise concern different
decision or shuffle questions. Source URLs, inspected ranges and hashes are
recorded in the [library note](../Library/Words/hughes2026a27755.md).
This is a bounded search result, not a worldwide absence claim.

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

An alphabet, arbitrary languages `A,B`, and a word of minimum depth
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

`D5/S1/Words/HughesIterationDepthNoGap.result` proves the conjecture for
every alphabet and arbitrary languages `A,B`: if a natural depth `r`
is attained, then every natural `q ≤ r` is attained. The literal insertion
factorization consists of `k` source factors and `k+1` base factors, each
possibly empty, with concatenations in `A` and in the preceding stage
respectively; the output is the interleaving `x₁y₁…xₖyₖxₖ₊₁`. Stage zero is
`B`. The existential positive degree can vary
between witnesses but is fixed throughout each witness's iteration history.
Minimum depth means absence at every earlier stage for every positive degree.
The proof requires no finiteness or countability of the alphabet, finiteness
of the languages, epsilon membership in `A`, or monotonicity in depth. Empty
alphabets, empty languages and epsilon-only languages are included; it asserts
no attained depth when the spectrum is empty.

The result is stated at `closedSourceZero`; its spectrum is extensionally
equal to the published zero-based spectrum.

The companion
`D5/S3/ConceptDynamics/InformationEscape/HughesIterationDepthNoGapRegistration`
registers the theorem's source depth origin through a finite two-origin arena,
with an inline realization bridge and a shifted-origin counterfactual for
variation and sensitivity. The arena's finiteness does not impose finiteness
on the alphabet or either language.
Only the S1 `result` Describe node carries the typed `Proved` claim for this
problem; the registration is not a second resolution.

Hughes retains credit for the conjecture, and the released project lead is
credited for selecting this already-screened target. The bounded prior-art
findings and access limits below do not establish worldwide priority.

## Triage

`theorem`. The result supplies the universal proof for arbitrary alphabets
and arbitrary languages, including empty and epsilon-only cases.

## ASSUMED-UNVERIFIED

The final publisher version of Ibarra–McQuillan (2025) was not compared with
the accepted manuscript. The Ito–Sugiura full chapter, Ito's older book, the
1981 Hughes–Selkow original and the 2005 CS-TR05 original remain outside
the verified literature scope; later public notes do not replace them.
Semantic Scholar was rate-limited and general search engines were unusable.
No claim is made about sources beyond the bounded search.
