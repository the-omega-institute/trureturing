---
slug: li-uncu-finite-andrews-gordon-companion
bibkey: li2025macmahon
doi: 10.48550/arXiv.2501.19272
url: https://arxiv.org/abs/2501.19272v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CylindricPartition/LiUncu.result
---

# A Finite Andrews–Gordon Companion Identity

## Problem

Runqiao Li and Ali K. Uncu, *A MacMahon Analysis View of Cylindric Partitions*, arXiv:2501.19272v1, Section 1,
Conjecture 1.3, equation (1.5): for integers n ≥ 0, k ≥ 5 and k > i ≥ 1,
Σ_{n₁≥⋯≥n_{k−1}≥n_k=0} q^{n₁²+⋯+n_{k−1}²+n_i+⋯+n_{k−1}} ∏_{j=1}^{k−1} [2n − 2Σ_{ℓ<j} n_ℓ − n_j − n_{j+1} − 2α_{ij} ;
n_j − n_{j+1}]′_q equals Σ_{r∈ℤ} (−1)^r q^{r((2k+1)r+2k−2i+1)/2} [2n ; n − (2k+1)r/2 + (2k−2i+1)((−1)^r − 1)/4]_q,
where α_{ij} = max(j − i + 1, 0), the Gaussian binomial vanishes unless its lower index lies between zero and the
upper index, and the primed one equals 1 when the lower index is zero, even for a negative upper index.

## Motivation

The theorem `D5/S3/Combinatorics/CylindricPartition/LiUncu.result` establishes (1.5) for every n ≥ 0, k ≥ 5 and
1 ≤ i < k.

## Gap

Pre-registration issue 12812 records the literature screen: the paper proves the cases k = 2, 3, 4, its citing paper
arXiv:2607.03912 does not treat the conjecture, and the repository had no claim on it. This is a bounded negative
finding.

## Route

1. A deletion–insertion bijection on weighted lattice paths with bounded height and a boundary state gives a
   recurrence for the multiple-sum side, with the doubled boundary shift and the primed convention.
2. The alternating side satisfies the same recurrence by q-Pascal identities for Gaussian binomials and explicit
   cancellations of image terms at the boundary.
3. Both sides agree at the initial values, and the recurrence determines its solution, which gives (1.5).

## Falsifier

The statement would fail if the boundary terms of the alternating side did not cancel in the recurrence, or if the
primed convention changed the initial values.

## Evidence

An independent referee implementation checked (1.5) coefficientwise for k = 5, …, 9, every 1 ≤ i < k and
n = 0, …, 9, and exhaustively checked the deletion and insertion maps on 1,799,175 paths.

## Triage

`theorem`; the statement is Conjecture 1.3 of arXiv:2501.19272v1, quantified over every n ≥ 0, k ≥ 5 and 1 ≤ i < k.

- Proved (formalized): equation (1.5) for every n ≥ 0, k ≥ 5 and 1 ≤ i < k.
- Proved (paper): the same path argument gives (1.5) for every k ≥ 2 and 1 ≤ i ≤ k, recovering the cases k = 2, 3, 4
  and the Foda–Quano identity i = k.
- Open: Conjecture 7.2 of the same paper, a coefficient nonnegativity statement for two alternating sums.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, its citing paper arXiv:2607.03912, web and GitHub searches and
the repository checks.
