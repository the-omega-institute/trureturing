---
slug: frid-2018-fibonacci-prefix-palindromic-length
bibkey: frid2018numerationpalindromes
doi: null
url: https://www.arxiv.org/abs/1710.11553
triage: theorem
motivation_gids:
  - D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result
---

# Frid's Fibonacci-prefix palindromic-length conjecture

## Problem

A. E. Frid, *Representations of palindromes in the Fibonacci word*, Numeration 2018 (Paris), Conjecture 2, states:

> For every k ≥ 1, the prefix of the Fibonacci word of length (100)²ᵏ⁻¹101 cannot be decomposed as a concatenation of at most 2k palindromes.

The numeral `(100)^(2k-1)101` is interpreted in the Fibonacci numeration system with weights `G(0)=1` and `G(1)=2`. `PL` is the minimum number of nonempty palindrome factors of a finite word.

## Motivation

The conjecture gives an explicit infinite family of prefixes whose palindromic length grows linearly in the numeral parameter. Its exact value determines the sharp lower bound and supplies the extremal family used by the associated limsup question.

## Gap

The cited abstract states the lower-bound conjecture without a proof. Ambrož, Kadlec, Masáková and Pelantová restate it as an open question in their study of palindromic length in Sturmian words. The missing step is a uniform lower bound for every factorisation of every member of the Frid family.

## Route

The Lean result defines the family `N(k)` and proves `PL(goldenFactor (N(k)) 0) = 2*k+1` for `k ≥ 1`. Canonical Fibonacci encodings are split into six-bit chunks. The palindrome endpoint necessity is proved by the reflected-mismatch certificate. A finite product potential bounds the score increase of every accepted palindrome edge by one, and the explicit Frid chunk cycle has score `2*k+1`; induction over a factorisation gives the lower bound. The symmetric central-word construction gives the matching upper bound.

## Falsifier

A value of `k ≥ 1` for which the prefix `goldenFactor (N(k)) 0` has a factorisation into at most `2*k` nonempty palindromes would refute the delivered equality. The endpoint necessity, product-potential inequality, and rank-cycle identity are the kernel-checked mechanisms excluding such a factorisation.

## Evidence

- Lean module: `D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.lean`.
- Settling declaration: `D5.S1.Words.FridPrefix.result`.
- The result compiles with the standard three axioms and the supporting endpoint, numeral, automaton, potential, and rank-cycle modules are frozen before this declaration.
- The source notes are `Library/Words/frid2018numerationpalindromes.md`, `Library/Words/frid2018sturmiannumeration.md`, and `Library/Words/ambrozetal2019palindromiclength.md`.

## Triage

`theorem`; the external named open problem is proved in the settling module under issue #13044. The public result keeps repository provenance because the source states Conjecture 2 without proof; its literature notes record the source and restatement. The exact value `2*k+1` is proved for every `k ≥ 1`. The endpoint rule necessity is proved in this delivery. The statement `PL(goldenFactor n 0) = S_A(n)` for every `n` is open; its finite computation is supporting evidence only. The exact global limsup constant remains open.

### What the settlement shows

The decisive mechanism is a finite rank potential on the endpoint product automaton together with the explicit Frid cycle. It proves the lower bound for every factorisation and reaches equality through the symmetric upper-bound construction. The endpoint necessity proof removes the unproved necessity gap in the source's stated palindrome rule. The same rank-and-cycle mechanism applies to the full Frid family; it does not by itself identify the exact palindromic length at arbitrary prefix indices or the exact limsup constant. Source questions that rely on the conjectured lower bound may now use the equality on this family, while those broader questions remain open.

## ASSUMED-UNVERIFIED

The literature search establishes the cited statements within the recorded sources and issue #13044; it is not an exhaustive worldwide novelty certificate. The source's use of the term “Fibonacci word” is identified with the repository's `goldenWord` through the stated morphism and indexing convention. The finite automaton tables are kernel-checked data, while the open all-index score identity and exact limsup constant are outside this settlement.
