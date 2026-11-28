---
slug: guyot-2024-square-root-state-complexity
bibkey: guyot2024state
doi: null
url: https://arxiv.org/abs/2407.10355v1
triage: theorem
motivation_gids:
  - D5/S0/Automata/DFAOStateLowerBound
  - D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.result
---

# Guyot's universal upper bound for square-root state complexity

## Problem

Section 2.2, Conjecture 1, of Jérôme Guyot's *On state complexity for
subword-closed languages* states
“$\forall n \in \mathbb{N}_{>0},\ \kappa(\sqrt{\downarrow(U_n)}) = \alpha(n) \leq c(n)^2-c(n)+3$.”
[arXiv:2407.10355v1](https://arxiv.org/html/2407.10355v1#Thmconjecture1)

**Mathematical scope.** The upper-bound conjunct quantifies over positive n,
finite alphabets and words w of length at most n. It asserts that the words x
for which xx is a scattered subsequence of w are recognized by a complete
DFA with at most c(n)² − c(n) + 3 states, where c(n) is the ceiling of n/3.
The quotient-count convention includes the empty quotient when it occurs.

## Motivation

Distinct continuations can force extra states in every complete recognizer.
The proposed bound constrains this mechanism uniformly in the input length.

## Gap

Remark 7 reports experimental checks for n ≤ 11. The first-tier
preregistration identifies the upper bound at n = 12 as the target for
a four-letter counterexample. [Issue #34977](https://github.com/the-omega-institute/trureturing/issues/34977)

## Route

Use the word abcdabcdabdc at n = 12, for which c(n) is 4 and the
bound is 15. The empty suffix and four one-letter suffixes yield distinct
acceptance patterns for sixteen selected prefixes. A test on a prefix and a
suffix asks whether the square of their concatenation is a scattered
subsequence of the word. By Mathlib's `Language.leftQuotient_accepts_apply`,
two prefixes that reach the same DFA state have the same continuation
language, so the sixteen patterns force sixteen states.

## Falsifier

A complete DFA with at most fifteen states accepting this square-root
language would contradict the injectivity of the sixteen reached states.
A collision among the sixteen computed patterns would invalidate this
certificate. Lean checks every pair against the five suffixes.

## Evidence

The formal predicate is `claim : Prop` and the frozen refutation is
`D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.result`.
The designated refutation result is exempt from four-slot escape registration
under §3.9. The motivation GID describes the related distinguishing-family
method for output automata. The proof uses the pinned Mathlib DFA API directly.
[Blueprint and proof](../Blueprint/D5/S0/Automata/GuyotSquareRootStateComplexityRefutation.md)
· [Literature note](../Library/Automata/guyot2024state.md)

## Triage

### What the settlement shows

- **Refuted.** The length-twelve language exhibits sixteen pairwise distinct left
  quotients, so the universal bound of fifteen at that length fails.
- **Source evidence.** Remark 7 reports the bound through n = 11.
- **Open here.** The exact maximum at n = 12, the proposed equality involving
  Uₙ, and a replacement universal bound lie outside this refutation.

## ASSUMED-UNVERIFIED

Independent publication priority remains unverified. The scoped literature
search recorded in issue #34977 leaves DBLP and OpenAlex coverage unverified.
