---
slug: benyi-mansour-ramirez-weak-ascent-210
bibkey: benyi2024pattern
doi: 10.46298/dmtcs.12273
url: https://arxiv.org/abs/2309.06518v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.result
---

# Weak Ascent Sequences Avoiding 210 and the Semi-Baxter Numbers

## Problem

Beáta Bényi, Toufik Mansour and José L. Ramírez, *Pattern Avoidance in Weak Ascent Sequences*,
arXiv:2309.06518v4 (Discrete Math. Theor. Comput. Sci. 26:1, 2024), Section 3, Conjecture 3.1:

> The sequence w_210(n) coincides with the sequence A117106.

The paper adds that A117106 enumerates permutations avoiding the vincular pattern 2-41-3. Here
w_210(n) counts the weak ascent sequences of length n with no indices i < j < k and e_i > e_j > e_k.

## Motivation

The theorem `D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.result` establishes, for every n, that
the 210-avoiding weak ascent sequences of length n and the permutations of [n] avoiding 2-41-3 are
equinumerous; both are counted by 1, 1, 2, 6, 23, 104, 530, 2958, 17734, … for n = 0, 1, ….

## Gap

Pre-registration issue 11728 records the literature screen: none of the located papers citing
arXiv:2309.06518 treats this conjecture, and OEIS A117106 records no proof. This is a bounded negative
finding.

## Route

1. For a nonempty 210-avoiding weak ascent sequence put H = 1 + wasc, M = max and D = the largest entry
   that is the smaller term of some inversion (0 if none). Appending x keeps the class exactly when
   D ≤ x ≤ H; moreover H ≥ M + 1 and the last entry is D or M.
2. Labelling a sequence by (M − D + 1, H − M) when it ends at its maximum and by (M − D, H − M + 1)
   otherwise, the labels of the children are those of the semi-Baxter succession rule
   (h, k) → (1, k + 1), …, (h, k + 1), (h + k, 1), …, (h + 1, k) with root (1, 1).
3. A 2-41-3-avoiding permutation stays in the class when its maximum is deleted; inserting a new maximum
   is allowed exactly at the active sites, and labelling by the active sites before and after the maximum
   gives the same succession rule.
4. Induction on the number of steps shows that every object with label (h, k) has the same number of
   descendants at each depth in both trees, so both classes have T(n − 1, 1, 1) members of length n ≥ 1.

## Falsifier

The statement would fail if some admissible append or active insertion produced a child label outside
the semi-Baxter rule, or if two distinct parents produced the same child.

## Evidence

The append criterion, the state updates and the children labels were checked on every 210-avoiding weak
ascent sequence and every 2-41-3-avoiding permutation of length at most 11; the counts agree through
n = 11.

## Triage

`theorem`; the statement is Conjecture 3.1 of arXiv:2309.06518 and is quantified over every n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the located citing papers, the OEIS entry, arXiv and GitHub searches
and the repository checks recorded above.
