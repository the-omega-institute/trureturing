---
bibkey: decastro2022binomialorders
authors: Dario T. de Castro
year: 2022
title: "p-Adic order of positive integers via binomial coefficients"
doi: null
url: https://math.colgate.edu/~integers/w61/w61.pdf
claim: "Conjectures 1 and 2 relate the p-adic order to the least common denominator of admissible binomial fractions; the OEIS A345531 comment predicts the first failure for composite bases."
strata_touched:
  - D5/S3/Arith/Congruence/DeCastroIntegersConjecture1
license: citation-only
triage: anchor
---

# Binomial fractions and adic orders

## Verified locator

Source: https://math.colgate.edu/~integers/w61/w61.pdf

INTEGERS 22 (2022), #A61, Section 3, p. 7.

## Source statements

Definition 2: “Let S^min_{p,n} and S^max_{p,n} denote sets of irreducible fractions given by S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ N*, j ∈ N, gcd(p_i^j, p) = 1, p_i^j ≤ n}, S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}.”

Definition 3: “A set S_{p,n} will be called admissible if it satisfies the condition S^min_{p,n} ⊆ S_{p,n} ⊆ S^max_{p,n}.”

Conjecture 1: “Given any admissible set S_{p,n}, the p-adic order of a positive integer n can be expressed as v_p(n) = log_p(n / L_{p,n}), where L_{p,n} represents the least common denominator of the elements of S_{p,n}.”

Conjecture 2: “Let q > 0 be a composite number, p_j a prime number that divides q, and c a non-negative integer. If we take n = q^c p_j, the evaluation of v_q(n) using (32) will fail for any admissible S_{q,n}.”

The indices i are positive and the exponents j include zero. Rationals represent irreducible fractions, and Finset.lcm Rat.den represents the least common denominator. Any admissible set is finite because it lies in Smax. The real logarithmic formula is interpreted with padicValNat and Real.logb.

## OEIS A345531

Source: https://oeis.org/A345531 (revision 70).

Name: “Smallest prime power greater than the n-th prime.”

Comment: “Take the family of correlated prime-indexed conjectures appearing in A343249 - A343253, in which an alternative formula for the p-adic order of positive integers is proposed. There, the general p-indexed conjecture says that v_p(n), the p-adic order of n, is given by the formula: v_p(n) = log_p(n / L_p(k0, n)), where L_p(k0, n) is the lowest common denominator of the elements of the set S_p(k0, n) = {(1/n)*binomial(n, k), with 0 < k <= k0 such that k is not divisible by p}. Evidence suggests that the primality of p is a necessary condition in this general conjecture. So, if a composite number q is used instead of a prime p in the proposed formula for the p-adic (now, q-adic) order of n, the first counterexample (failure) is expected to occur for n = q * a(i), where i is the index of the smallest prime that divides q.”

For composite q, excluding multiples of q differs from requiring gcd(k,q)=1. Success in the OEIS statement means existence of a cutoff k0 in [1,n].

## Computation and literature boundary

The independent exact-integer checker is in the private repository `the-omega-institute/trureturing-experiments`, commit `868cd5a4bfc892973540526d582483fba6d039c1`, at `docs/reports/oeis-a343249-a343253-a345531-de-castro-p-adic-order/check.py`. Its SHA256 is `edd3b71e1df8d451fd19a771e0d82b399c4f32d27370de96a9c69a0082007706`. The reported command `python3 check.py 400 200` exited 0 with final line `RESULT PASS`. These bounded calculations do not prove an unbounded claim.

The literature screen in issues #18681, #18683 and #18684 covers the paper, the OEIS mirror, and arXiv:2209.14236v11. No settlement was found in that searched scope. Literature completeness and external priority are ASSUMED-UNVERIFIED.
