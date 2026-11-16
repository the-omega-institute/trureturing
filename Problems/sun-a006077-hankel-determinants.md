---
slug: sun-a006077-hankel-determinants
bibkey: sun2013a006077
doi: 10.48550/arXiv.1308.2900
url: https://arxiv.org/abs/1308.2900v5
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hankel/SunA006077Blocks
  - D5/S3/Combinatorics/Hankel/SunA006077Arithmetic
  - D5/S3/Combinatorics/Hankel/SunA006077Positivity
---

# Sun's Conjecture 3.16 on the A006077 Hankel determinants

## Problem

Zhi-Wei Sun, [*On some determinants with Legendre symbol entries*](https://arxiv.org/pdf/1308.2900v5), arXiv:1308.2900v5, p. 17, Conjecture 3.16, defines for every $n\ge 0$

$$
w_n=\sum_{k=0}^{\lfloor n/3\rfloor}(-1)^k3^{n-3k}
\binom{n}{3k}\binom{2k}{k}\binom{3k}{k},
\qquad W(n)=\det[w_{i+j}]_{0\le i,j\le n}.
$$

The conjecture asserts $W(n)=0$ for $n\equiv1\pmod3$. For $n\equiv0,2\pmod3$, it asserts that $(-1)^{\lfloor(n+1)/3\rfloor}W(n)/6^n$ is a positive odd integer. Equivalently, in those two residue classes there exists $z\in\mathbb Z$ with $z>0$, $z$ odd, and $(-1)^{\lfloor(n+1)/3\rfloor}W(n)=6^n z$. This formulation includes $n=0$ and uses the literal finite sum identified in Remark 3.16 with [OEIS A006077](https://oeis.org/A006077).

## Motivation

The sign and normalization vary with the residue class. A block decomposition explains both the exact zero class and how two moment determinants control the two nonzero classes. Their parity and positivity require different information: reduction modulo two detects nonsingularity, while real moment forms control the sign.

## Gap

[Sun's v6 Remark 3.16](https://arxiv.org/pdf/1308.2900v6) credits C. Krattenthaler with the entire zero class. Sun's *Open Conjectures on Congruences*, [DOI 10.3969/j.issn.0469-5097.2019.01.01](https://doi.org/10.3969/j.issn.0469-5097.2019.01.01), Conjecture 81(i), retains the nonzero assertion. The bounded literature screen in [#28973](https://github.com/the-omega-institute/trureturing/issues/28973) found established ingredients and no complete published proof in the sources it inspected.

## Route

Put $c_r=\binom{2r}{r}\binom{3r}{r}$, with sparse moments $b_{3r}=(-1)^r c_r$ and $b_{3r+1}=b_{3r+2}=0$. The finite sum is the weighted binomial transform of $b$. Its Hankel determinant is unchanged by that transform. Grouping rows and columns by residue modulo three gives an unshifted block and two cross blocks from shifted moments. Write $D_k=\det[c_{i+j}]_{0\le i,j<k}$ and $E_k=\det[c_{i+j+1}]_{0\le i,j<k}$, with the empty determinant equal to one. Then

$$
W(3m)=(-1)^mD_{m+1}E_m^2,\qquad
W(3m+1)=0,\qquad
W(3m+2)=(-1)^{m+1}D_{m+1}E_{m+1}^2.
$$

Row factorization gives integral quotients $d_m=D_{m+1}/6^m$ and $e_m=E_m/6^m$. For $r>0$, $c_r/6$ is odd precisely when $r$ is a power of two, including $2^0$. Modulo two the normalized determinants reduce to the two Rueppel families, so $d_m$ and $e_m$ are odd. A beta moment factorization and the Schur product give positive semidefinite real moment matrices. The odd quotients make both determinants nonzero, hence the matrices are positive definite and the quotients are positive. The signed quotients of $W$ are $d_m e_m^2$ and $d_m e_{m+1}^2$ in the two nonzero classes.

## Falsifier

A natural index in the zero class with $W(n)\ne0$, or one in either other class for which the signed quotient fails integrality, strict positivity, or oddness, would refute the corresponding clause. The result proves both clauses for every natural index.

## Evidence

The exact Lean declaration is `D5/S3/Combinatorics/Hankel/SunA006077Result.result`. Its statement uses the integral witness identity above. The supporting statements cover the literal transform, residue blocks, normalized parity and positive semidefiniteness for every nonnegative shift and finite size.

Literature ingredients: [Spivey and Steil, Theorem 6.1](../Library/Eigenstructure/spivey2006binomial.md) for weighted binomial Hankel invariance; [Cigler, Theorems 1.1 and 2.1](../Library/Eigenstructure/cigler2018curious.md) for the ordinary and once-shifted Rueppel determinant evaluations, used here modulo two; [Penson and Solomon, equation (6) and Example 9](../Library/Eigenstructure/penson2001coherent.md) for the positive moment representation of $c_r$. Sun's [source note](../Library/Eigenstructure/sun2013a006077.md) records the separate attribution of the zero branch.

## Triage

- Proved in Lean: `D5/S3/Combinatorics/Hankel/SunA006077Result.result` establishes the full v5 assertion. `SunA006077Blocks.block_zero`, `block_two`, and `zero_branch` records the three residue cases, including the previously known zero class.
- Proved in Lean: `SunA006077Positivity.multinomial_posSemidef` establishes positive semidefiniteness for every nonnegative shift of the multinomial moments. `SunA006077Arithmetic.normalized_odd` proves oddness of the two normalized determinants; combined with positive semidefiniteness, it rules out singularity for the shifts used in the conjecture.
- Outside this result: the separate prime congruence in later versions of Sun's paper and in Conjecture 81(ii) has a different conclusion.

## ASSUMED-UNVERIFIED

The bounded search does not settle worldwide priority. Full OEIS revision history, the original Number Theory List message body, and inaccessible or unindexed publications were not verified in the literature screen.
