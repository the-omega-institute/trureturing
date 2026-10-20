---
bibkey: phunphayap2023digitsumarcs
authors: P. N. Phunphayap; P. Noppakaew; P. Pongsriiam
year: 2023
title: Directed graphs of integers with arcs determined by an arithmetic function
doi: 10.61091/um124-06
url: https://arxiv.org/abs/2303.13017v1
claim: "Question 3 asks for a necessary and sufficient condition for infinitely many outgoing digit-sum arcs not divisible by the digit sum of n, and for their natural density."
strata_touched:
  - D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs
license: citation-only
triage: anchor
---

# Outgoing digit-sum arcs

The source is arXiv:2303.13017v1, also published in Utilitas Mathematica
124 (2025), 101–114. The published version retains the question as Question 3.3.

## Verified locator

DOI: 10.61091/um124-06

Source: https://arxiv.org/abs/2303.13017v1

## Source definitions

Page 2 defines an arc:

> We say that there exists a g-directed edge or g-arc from n to u if there exists a positive integer N such that N is divisible by n and g(N) = u.

It then defines:

> Out(g, n) = {u ∈ ℕ | n →g u}.

Here ℕ denotes positive integers. The formal set therefore requires both
`0 < u` and `0 < N`. For the base-b digit sum it uses
`(Nat.digits b N).sum`. Page 3 gives the examples s₁₀(123) = 6 and s₅(123) = 11;
all digits, including the units digit, are counted.

## Question 3

Page 10 asks:

> We obtain in Theorem 2 that Out(s_b, n) contains every multiple of s_b(n). Does Out(s_b, n) contain an infinite number of positive integers that are not divisible by s_b(n)? When d = 1 and s_b(n) ≥ 2, the answer is yes. Can we determine a simple necessary and sufficient condition for the infinitely many elements in A ∩ Out(s_b, n) where A is the set of positive integers that are not divisible by s_b(n)? In that case, does Out(s_b, n) has a natural density?

The repository answer concerns all b ≥ 2 and n ≥ 1. It states that the set in the
question is infinite exactly when gcd(b−1,n) < s_b(n), and that Out has natural
density 1/gcd(b−1,n). The density counts the inclusive positive interval [1,x].
The proof also establishes qualitative cofiniteness among positive multiples of
the gcd. It supplies no explicit saturation threshold or sharp Frobenius number.

The definitions and question belong to the source. The answer and its proof are
repository-derived. Prior-art completeness is ASSUMED-UNVERIFIED.
