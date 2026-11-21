# The signed A400645 rule for every nondecreasing seed

## Abstract

For every nondecreasing seed the signed A400645 rule has nonnegative radicands, and a_n = c λ^n + O(1) with c > 0 unless the seed is (0,0,0,0) or (1,1,1,1).

**Theorem 1.1 (Classification of nondecreasing seeds).**

Lean statement: `D5/S1/Recurrence/OEISA400645LargeSeeds.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/OEISA400645LargeSeeds.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

Let a_1 ≤ a_2 ≤ a_3 ≤ a_4 be nonnegative integers and, for n ≥ 4, a_(n+1) = round √s_n with s_n = a_n^2 + a_(n−1)^2 + a_(n−2)^2 − a_(n−3)^2. Let r be the largest real root of y^4 − y^3 − y^2 − y + 1 and λ = √r. Then (i) s_n ≥ 0 for every n ≥ 4, so the rule is well defined; (ii) the seeds (0,0,0,0) and (1,1,1,1) give constant sequences; (iii) for every other seed there is c > 0 with a_n − c λ^n = O(1) and a_(n+1)/a_n − λ = O(λ^(−n)). The two constant seeds are exactly the seeds for which (iii) fails.

Proof. By strong induction the sequence is nondecreasing from index one: a_(n−2) ≥ a_(n−3) gives s_n ≥ a_n^2, so a_(n+1) ≥ √s_n − 1/2 ≥ a_n − 1/2 and hence a_(n+1) ≥ a_n. This also gives (i). For (ii), a constant window c, c, c, c has s_n = 2c^2, and round √0 = 0, round √2 = 1. If a_n ≥ 3 for some n ≥ 4, then s_n ≤ 3 a_n^2 ≤ (7a_n/4)^2, so a_(n+1) ≤ 7a_n/4 + 1/2; since s_(n+1) ≥ a_(n+1)^2 + a_n^2 and a_n^2 > a_(n+1) + 1/4, one gets √s_(n+1) > a_(n+1) + 1/2 and a_(n+2) > a_(n+1). Hence once a term reaches 3 the sequence tends to infinity.

Every seed other than the two constant ones reaches 3. If all terms stayed at most 2, a term equal to 2 would be followed by a window 2, 2, 2, 2 with s = 8 and next term round √8 = 3. If all terms stayed at most 1, then a_1 = 0 and a_4 = 1, so some a_k = 0 is followed by three ones, giving s = 3 and next term round √3 = 2.

For (iii) put b_n = a_n^2. Then b_j − b_(j+1) − b_(j+2) − b_(j+3) + b_(j+4) = a_(j+4)^2 − s_(j+3) = e_j with |e_j| ≤ √s_(j+3) + 1/4 ≤ √(b_j + b_(j+1) + b_(j+2) + b_(j+3)) + 1/4. Once a_n ≥ 10, b_(n+3) ≤ (8/7)(b_n + b_(n+1) + b_(n+2)) and (9/10)(b_n + b_(n+1)) ≤ b_(n+2). The constants satisfy (8/7)(1 + 2 + 4) = 2^3, (3/2)^2 = (9/10)(1 + 3/2) and 2 < min(r^2, (3/2)^2). The root r is simple and the other roots have modulus below √r < √2 (D5/S1/Recurrence/OEISA400645BoundedError). The analytic core of D5/S1/Recurrence/RoundedNormBoundedError then gives b_n = L r^n + O(r^(n/2)) with L > 0, and rationalizing gives (iii) with c = √L. If the seed is constant, a bounded sequence cannot be within O(1) of c λ^n with c > 0 and λ > 1.

This is Corollary 4 in Section 4 of H. Ma and W. Zhang's note on OEIS A400645 (DOI 10.5281/zenodo.24369110), which assumes a_4 ≥ 292 and gives the bounded error. Here the threshold is replaced by the exact condition on the seed, and the ratio rate is added.

## References

- Truth anchor: `D5/S1/Recurrence/OEISA400645LargeSeeds.result`
- Dependency: [D5/S1/Recurrence/OEISA400645BoundedError](OEISA400645BoundedError.md)
- Dependency: [D5/S1/Recurrence/RoundedNormBoundedError](RoundedNormBoundedError.md)
