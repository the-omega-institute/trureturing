---
slug: kasel-2026-displacement-ladder
bibkey: kasel2026erdos197
doi: 10.48550/arXiv.2609.02939
url: https://arxiv.org/abs/2609.02939v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/KaselDisplacementLadder.result
---

## Problem
Kasel, arXiv:2609.02939, Appendix B.4, states: “The conjectured growth L(m) = m − 2”. The exact target was preregistered in [#14885](https://github.com/the-omega-institute/trureturing/issues/14885).

Let $b(v)=\lceil\log_2 v\rceil$ for $v\ge2$, implemented by the total natural-number function `Nat.clog 2 v`. Set

$$S_A(m)=\{v\in[1,4^m]:b(v)\ge2,\ b(v)\text{ even}\},\qquad
D=\{3,4,9,10,11,12,13,14,15,16\}.$$

A scheme consists of natural-valued stages $s$ and fibre positions $r$. It orders values by stage, then by fibre position. Validity requires injectivity within each stage and excludes both increasing and decreasing three-term arithmetic progressions in that concatenation. Normalization requires $s(v)\ge\lfloor b(v)/2\rfloor$ on $S_A(m)$. Write $\delta(v)=s(v)-\lfloor b(v)/2\rfloor$ and let $L(m)$ be the minimum, over valid normalized schemes, of $\max_{v\in D}\delta(v)$. The proved statement is $L(m)=m-2$ for every natural $m\ge2$.

## Motivation
The displacement ladder measures the finite-horizon structural obstruction behind Erdős Problem 197. Its exact growth quantifies the obstruction already supplied by the repository's frozen Erdos-Graham order-gadget theorem.

## Gap
The literature readings recorded for preregistration found only arXiv v1; the author's TeX still labels the growth conjectural. Searches on Kasel, displacement ladder and L(m) found no resolution. The `formal-conjectures` file `ErdosProblems/197.lean` states only the parent problem. The repository's earlier order-gadget theorem supplies the lower-bound obstruction. The remaining upper construction and its matching lower-bound transfer are now proved in Lean. These readings delimit the searched material; they do not establish an exhaustive originality claim.

## Route
For the upper bound, put 3 and 4 at stage one and all other values at stage $m$. Order evens before odds, using reversal of the lowest $2m+1$ bits after XOR with target 4 for evens and target 3 for odds. The bounded numeric rank is injective and puts each target first. A recursive parity argument excludes a middle term between its endpoints in rank order. The dyadic gap excludes an AP starting at 3 with a later even middle term. These facts prove validity, while block bounds prove normalization and distinguished displacement at most $m-2$.

For the lower bound, $m=2$ follows from normalization at 3. For $m\ge3$, assume both 15 and 16 have stage below $m$, and set $M=2\cdot4^{m-1}$. Every value in $(M,2M]$ lies in block $2m$ and has stage at least $m$. Counting predecessors gives a rank preserving and reflecting the valid concatenation order. Its AP exclusion and forced guard comparisons form the forbidden order gadget at $M\ge32$. Hence 15 or 16 has stage at least $m$, giving distinguished displacement at least $m-2$. Combining the two bounds proves the exact claim.

## Falsifier
A normalized valid scheme at some horizon $4^m$, $m\ge2$, with all distinguished displacements below $m-2$ would contradict the lower bound. Failure of existence of a normalized valid scheme with all distinguished displacements at most $m-2$ would contradict the upper bound. For an integer cap $w\ge0$, the equivalent first-failure exponent is $m=w+3$.

## Evidence
`KaselDisplacementLadderDefs` fixes the definitions and dyadic membership lemmas. `KaselDisplacementLadderLower.lower_bound` proves the universal distinguished lower bound using the frozen `ErdosGrahamOrderGadget.result`. `KaselDisplacementLadderUpper.upper_bound` constructs an attaining normalized valid scheme. `KaselDisplacementLadder.result : claim` combines both bounds. These declarations lie under `D5.S3.Combinatorics.Permutation`; their corresponding Blueprint Scribes describe the definitions and proofs, and the result node declares a Proved resolution of this problem slug.

## Triage
- [proved] For integer $w\ge0$ and natural $m\ge2$, a normalized valid scheme at horizon $4^m$ with every distinguished $\delta\le w$ exists if and only if $m\le w+2$. This follows from the matching bounds.
- [proved] $L(m)\to\infty$, which re-derives Theorem 44's conclusion for $S_A$, already known through the order gadget.
- [open] Erdős #197 itself.

## ASSUMED-UNVERIFIED
The literature readings above are carried from preregistration; no fresh external search was performed for this delivery because network access is unavailable. The first-failure equivalence and divergence are consequences of the exact proved bounds, rather than separate named Lean declarations. The Lean result resolves the displacement-ladder claim with the definitions stated above; it does not resolve the parent Erdős problem.
