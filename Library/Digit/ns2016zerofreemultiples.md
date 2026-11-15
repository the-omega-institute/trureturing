---
bibkey: ns2016zerofreemultiples
authors: N. S.
year: 2016
title: "Answer to Integers n for which all multiples of n contain a zero digit"
doi: null
url: https://math.stackexchange.com/a/2067782
claim: "A positive integer has a zero-free decimal multiple if and only if it is not divisible by ten."
strata_touched:
  - D5/S1/Digit/MurthyA085124
license: citation-only
triage: anchor
---

# Zero-free decimal multiples

The answer's Claims 1 and 2 and the author's induction comment supply
zero-free suffixes divisible by arbitrary powers of two or five. Appending
a leading digit solves one new congruence because the remaining coefficient
is invertible modulo the selected prime. Repetition of a block handles the
factor coprime to ten. These mechanisms are literature-attested prior work.
The Lean proof uses Euler's theorem and a geometric sum for the repetition
step, and enriches the block with a word of prime factors to control its digit
product. Neither the prior suffix helper nor repetition alone states the
joint digit-product classification.

## Verified locator

- URL: https://math.stackexchange.com/a/2067782
- Author's lifting comment: https://math.stackexchange.com/questions/2067752#comment4448589_2067782

## Attribution boundary

No upstream Lean source is copied. This note cites the mathematical mechanism;
the repository supplies its Lean implementation and the prime-factor-word
application. The helper is not presented as a novel theorem of this repository.
