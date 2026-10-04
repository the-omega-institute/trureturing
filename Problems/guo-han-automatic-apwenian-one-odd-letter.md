---
slug: guo-han-automatic-apwenian-one-odd-letter
bibkey: guo2025apwenian
doi: 10.1016/j.disc.2025.114399
url: https://irma.math.unistra.fr/~guoniu/papers/p120autoapw.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Apwenian/GuoHan.result
---

# Purely Automatic Apwenian Sequences over an Alphabet with One Odd Letter

## Problem

Ying-Jun Guo and Guo-Niu Han, *On a family of automatic apwenian sequences*, Discrete Mathematics 348 (2025) 114399,
Conjecture 2. A sequence a over ℕ is apwenian if a(0) = 1 and a(n) ≡ a(2n+1) + a(2n+2) (mod 2) for every n. Let Σ be
a finite set of nonnegative integers whose only odd element is 1, and let a be a fixed point of a p-uniform morphism on
Σ with p ≥ 2. The conjecture states that a is apwenian if and only if a(n) ≡ P(n) (mod 2) for every n, where P is the
period-doubling sequence, the fixed point of 1 ↦ 10, 0 ↦ 11.

## Motivation

The theorem `D5/S3/Combinatorics/Apwenian/GuoHan.result` establishes the equivalence for every such alphabet and
every p ≥ 2.

## Gap

Pre-registration issue 12861 records the literature screen: the paper proves the case Σ = {0, 1, 2}, and searches of
arXiv, the apwenian literature (arXiv:2001.10246, 1601.04370, 2008.12160) and the repository found no proof of the
general case. This is a bounded negative finding.

## Route

1. Since 1 is the only odd letter, b(n) = a(n) mod 2 equals 1 exactly when a(n) = 1, so every parity-one position
   carries a copied block of the iterated morphism.
2. Iterating the apwenian relation gives b(n) = Σ_{j<D} b(D(n+1) − 1 + j) for every power of two D; a copied block
   at a position divisible by D therefore contracts to a shorter copied block.
3. The prefix of a is 1, an even letter, 1, for every finite alphabet.
4. If p has an odd factor d₀ ≥ 3, contracting the copied blocks of lengths p² and p⁴ on the letter at position 2 forces
   an index N with b(N) = b(N) + 1, a contradiction; hence p is a power of two.
5. For p a power of two, the contraction gives b(n) = 1 ⇒ b(2n) = 1, and a least even zero cannot exist; then the
   apwenian relation gives b(2n+1) = 1 − b(n), which is the period-doubling recursion.

## Falsifier

The statement would fail if some apwenian fixed point had a parity sequence different from the period-doubling
sequence, for instance for a uniform length with an odd factor.

## Evidence

An independent referee implementation enumerated every morphism on alphabets of size at most 3 with lengths at most 4,
on alphabets of size 4 with lengths at most 3, and on two-letter alphabets with mixed lengths 6 and 10, testing the
statement and each lemma on prefixes of length at least 2048.

## Triage

`theorem`; the statement is Conjecture 2 of the paper, quantified over every finite alphabet whose only odd letter is
1 and every p ≥ 2.

- Proved (formalized): the equivalence for every such alphabet and every p ≥ 2.
- Proved (paper): an apwenian fixed point of this kind exists only when p is a power of two.
- Computed: Lemma 7 of the paper is false as printed (the apwenian prefix 110011111 satisfies its right-hand
  condition but is not period-doubling); the paper's use of it is protected by its earlier prefix hypothesis, and the
  proof above does not use it.
- Open: Conjecture 1 of the paper, the representation of every binary 2-automatic apwenian sequence by a directive
  sequence over a finite alphabet.

## ASSUMED-UNVERIFIED

The literature screen is limited to the author version of the paper, the arXiv apwenian literature, web and GitHub
searches and the repository checks.
