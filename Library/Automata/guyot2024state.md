---
bibkey: guyot2024state
authors: Jérôme Guyot
year: 2024
title: On state complexity for subword-closed languages
doi: null
url: https://arxiv.org/abs/2407.10355v1
claim: Conjecture 1 gives an extremizing word and a universal upper bound for the quotient complexity of square roots of subword closures.
strata_touched:
  - D5/S0/Automata/GuyotSquareRootStateComplexityRefutation
license: CC BY 4.0
triage: anchor
---

# Square-root state complexity of subword closures

## Verified locator

https://arxiv.org/abs/2407.10355v1

Section 2.2, Conjecture 1, states
“$\forall n \in \mathbb{N}_{>0},\ \kappa(\sqrt{\downarrow(U_n)}) = \alpha(n) \leq c(n)^2-c(n)+3$.”
Here c(n) is the ceiling of n/3 and α(n) is the maximum quotient count for
the square roots of the subword closures of words of length at most n.
The conjectured extremizer Uₙ consists of two copies of the distinct-letter
prefix of length c(n) followed by the prefix of length n − 2c(n).
Section 1 counts the distinct left quotients, including the empty quotient
when it occurs. Section 2.2 uses the square-root operation that tests whether
two consecutive copies of a candidate word belong to the underlying language.
Remark 7 reports experimental checks of the bound through n = 11.
[Conjecture 1 and Remark 7](https://arxiv.org/html/2407.10355v1#Thmconjecture1)
