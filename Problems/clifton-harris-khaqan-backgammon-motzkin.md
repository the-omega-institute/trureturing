---
slug: clifton-harris-khaqan-backgammon-motzkin
bibkey: cliftonharriskhaqan2026parking
doi: 10.48550/arXiv.2611.29890
url: https://arxiv.org/pdf/2611.29890v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_signed_motzkin
---

# Question 5.2 on increasing-prefix backgammon outcomes

## Problem

Alexander Clifton, Pamela E. Harris and Maryam Khaqan, *Parking Functions
inspired by board games*, arXiv:2611.29890v1, §5, Question 5.2, p. 27
(transcribed with mathematical notation).

> For fixed $k\in\mathbb N$, can $|O_B^{-1}(12\cdots(k-1)(k)(n)(n-1)\cdots(k+2)(k+1))|$ for $n>k$ be expressed as a sum involving Motzkin numbers whose indices depend on $n$?

An arrival takes its preferred slot and sends its incumbent, if any, to the
least vacant slot. The outcome lists car labels in slot order. Proposition 1.5
identifies the length-$n$ preference domain with $[n]^n$.
[Primary source](https://arxiv.org/pdf/2611.29890v1#page=27)

## Motivation

The frozen theorem gives an explicit integer combination of ordinary Motzkin
counts for every fixed increasing prefix. Its coefficients depend only on the
prefix length, and the largest index is $n+k$.

## Gap

Theorem 1.8 and Corollaries 1.9–1.10 give the answers for $k=0,1,2$ on their
stated ranges. Lemma 3.18, equation (5), and the proof of Theorem 1.8 supply
the refined reverse-outcome recurrence and its Motzkin interpretation.
Theorem 1.6 supplies the identity-outcome Catalan count for $n>0$.
Question 5.2 asks for the arbitrary fixed prefix.
[Primary source](https://arxiv.org/pdf/2611.29890v1) ·
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/35186)

## Route

Let $B_k(r)$ count the $k$ successive prefix lifts of a word of rank $r$, and
let $C_i=B_i(0)$. The insertion fibers give $B_0(r)=1$ and
$B_{k+1}(r)=\sum_{s=1}^{r+1} B_k(s)$. One extra return changes the weight
to $B_k(r+1)=\sum_{i=0}^k C_i B_{k-i}(r)$. At $r=0$ this gives the
Catalan convolution.

Let $W_k(m)$ be the sum of $B_k$ over length-$m$ Motzkin walks, using arrivals
at height zero as rank. The horizontal-step and first-arch decomposition gives
$W_{k+1}(m)+\sum_{i=0}^k C_i W_{k-i}(m+1)=W_k(m+2)$.
Thus $Q_0=1$ and $Q_{k+1}=T^2Q_k-T\sum_{i=0}^k C_iQ_{k-i}$, with
$F_k(n)=\sum_{j=0}^{2k}[T^j]Q_k\,M_{n-k+j}$ for $n\ge k\ge0$.
The shift polynomial relative to $n$ is $P_k=T^{-k}Q_k$. The leading
coefficient is one, and for $k>0$ the constant coefficient of $Q_k$ is zero.

## Falsifier

A preference word mapped into or out of the literal fiber by an incorrect
deletion or insertion, a Motzkin scan admitting a down step from zero, or a
valid pair $(n,k)$ for which the signed sum differs from the fiber count would
invalidate the corresponding claim.

## Evidence

The frozen declaration
`D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.increasingPrefix_count_eq_signed_motzkin`
checks the exact integer-cast fiber formula for all naturals with $k\le n$.
The published question has the strict bound $n>k$. The verified statement
therefore includes the question and extends to the diagonal $n=k$, where the
suffix is empty and both sides equal the Catalan value $C_k$, including
$F_0(0)=C_0=1$.

The Lean declarations establish the literal outcome enumeration, the literal
Motzkin-walk correspondence, the weighted reverse-outcome bridge, the signed
coefficient recurrence, and the coefficient support and leading term.

The four-slot audit covers 27 public theorems. The retained registration for
`signedCoefficients_shape` validates. Two further typed attempts reached
`IE-C050` at `Nat.pow`, and 24 source forms lack compiled binding evidence.
[Owner audit disclosure](https://github.com/the-omega-institute/trureturing/issues/35186#issuecomment-7236512926)

## Triage

- Proved in Lean: the signed Motzkin formula for every $n\ge k\ge0$, hence for the published range $n>k$.
- Proved in Lean: the diagonal value at $n=k$, including the empty case $F_0(0)=C_0=1$.
- Proved in Lean: the coefficient list has length $2k+1$, leading coefficient one, and zero constant coefficient for positive $k$.
- The checked length and zero constant coefficient imply that the nonzero
  shifts from $n$ lie in $[1-k,k]$ when $k>0$.
- The four-slot registration audit remains unfinished for 26 of its 27 targets.

## ASSUMED-UNVERIFIED

The literature screen covers the primary arXiv record, the arXiv query for
backgammon and Motzkin, the zbMATH title search and the first five Crossref
bibliographic results. It found no separate resolution of Question 5.2.
OpenAlex returned HTTP 429. The screen gives bounded provenance evidence.
