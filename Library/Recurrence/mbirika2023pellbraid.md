---
bibkey: mbirika2023pellbraid
authors: aBa Mbirika; Janee Schrader; Jürgen Spilker
year: 2023
title: "Pell and Associated Pell Braid Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and Related Numbers"
doi: 10.48550/arXiv.2301.05758
url: https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.pdf
claim: "Conjecture 32: gcd(Q_k, k) > 1 if and only if a prime divisor p of k has entry point e_Q(p) dividing k."
strata_touched:
  - D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation
license: citation-only
triage: anchor
---

# Associated Pell gcds and entry points

aBa Mbirika, Janee Schrader, and Jürgen Spilker published this article in
Journal of Integer Sequences 26 (2023), Article 23.6.4. Definition 3, on
printed page 4, states verbatim:

> **Definition 3.** The Pell sequence (P_n)_{n≥0} and the associated Pell sequence (Q_n)_{n≥0} are defined by the recurrence relations P_n = 2P_{n−1} + P_{n−2} and Q_n = 2Q_{n−1} + Q_{n−2}, respectively, with initial conditions P_0 = 0, P_1 = 1, Q_0 = 1, and Q_1 = 1.

The module reuses `D5/S1/Recurrence/PellCompanionGcd.Q`, whose initial values
and recurrence are exactly this associated Pell sequence.

Section 6.1, on printed page 22, introduces the entry point verbatim:

> When (S_n)_{n≥0} is the Pell or associated Pell sequence, we have partial results towards closed forms for gcd(S_k, k) that involve the entry point (or rank of apparition), e_S(p), which is the smallest index r > 0 such that p divides S_r where p is a prime.

The same section states the conjecture verbatim:

> **Conjecture 32.** We claim that gcd(Q_k, k) > 1 if and only if there exists a prime p such that p divides k and the rank of apparition (or entry point), e_Q(p) divides k. For example, gcd(Q_21, 21) = 7 and for the prime p = 7, we have p divides 21 and e_Q(p) = 3 divides 21.

The entry-point phrase is read as requiring a least positive index to exist.
At `k = 12`, the associated Pell value is `Q_12 = 19601`, so its gcd with
12 is 1. The prime 3 nevertheless divides 12 and has entry point 2 because
`Q_1 = 1` and `Q_2 = 3`; moreover, 2 divides 12. This refutes the printed
biconditional. No corrected statement is asserted.

The journal article, arXiv version 2301.05758v3, cited records, and the 2025
Fiebig-Mbirika-Spilker Lucas-sequence paper were checked for a later proof or
refutation of Conjecture 32; none was found in that scope.

## Verified locator

- DOI: 10.48550/arXiv.2301.05758
- URL: https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.pdf
- Scope: Definition 3 on printed p. 4 and Conjecture 32 in section 6.1 on printed p. 22.
