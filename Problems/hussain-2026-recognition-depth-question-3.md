---
slug: hussain-2026-recognition-depth-question-3
bibkey: hussain2026decisiontrees
doi: 10.48550/arXiv.2611.27454
url: https://arxiv.org/abs/2611.27454v1
triage: theorem
motivation_gids:
  - D5/S3/Observer/Budget/HussainRecognitionDepth.result
---

# Hussain Question 3 on deterministic recognition depth

## Problem

Shahid Hussain, *Decision trees for subword-closed languages over arbitrary
finite alphabets*, arXiv:2611.27454v1, §6, asks:

> In case (c), is $h^{\mathrm{rd}}_L(n)$ eventually constant?

For every finite alphabet $A$ of size at least two and every language
$L\subseteq A^*$ closed under scattered subwords with finite Hom and
Het, the claim is that there are $N\ge1$ and $d\ge0$ such that
$h^{\mathrm{rd}}_L(n)=d$ for all $n\ge N$.
[Question 3](https://arxiv.org/html/2611.27454v1#S6.I1.i3.p1.1) · [Theorem 1](https://arxiv.org/html/2611.27454v1#Thmtheorem1) · [Issue #33567](https://github.com/the-omega-institute/trureturing/issues/33567)

| Source clause | Lean counterpart |
| --- | --- |
| Finite alphabet of size at least two | An arbitrary `Fintype Alphabet` with `2 ≤ Fintype.card Alphabet`. |
| Scattered-subword closure | `SubwordClosed` uses `List.Sublist`. |
| Finite Hom and Het | `HomExponents` and `HetExponents` use the exact two patterns and distinct letters. The claim requires both exponent sets to be finite. |
| Length-$n$ promise | `Promise` uses `Fin n → Alphabet` and `List.ofFn`. |
| Determinism and legal leaves | `SourceTree` represents the subtree entered by the unique unlabeled root edge. Each query has a nonempty set of present letter branches, and terminal labels belong to the promise. |
| Coverage and correctness | `Recognizes` requires a compatible complete path for every promised input and the correct label on every compatible complete path. |
| Worst-case depth and empty promise | `DepthLE` quantifies over all complete paths. `recognitionDepth` minimizes the feasible budget, with depth zero available when the promise is empty. |
| Eventual equality | `claim` quantifies $N,d$ over the natural numbers, requires $1\le N$, and asserts equality at every $n\ge N$. |

## Motivation

The uniform bound in Theorem 1(c) controls the possible depths. Eventual
equality determines that these values settle permanently along the
sequence of length promises.

## Gap

The source poses the tail equality. The literature screen recorded for
the problem identifies uniform bounds in Hussain and in the cited
binary case of Moshkov. It reports no exact prior settlement in the
sources examined. Literature completeness remains unverified.
[Issue #33567](https://github.com/the-omega-institute/trureturing/issues/33567)

## Route

A source tree yields an adaptive protocol at the same depth bound by
completing missing branches with leaves. Conversely, an adaptive
protocol yields a source tree of the same depth bound by labeling each
realized leaf with the unique input producing its transcript. Remaining
leaves use a fixed promised word when the promise is nonempty. Coordinate
queries and the empty-promise convention give equality of the minima.

Let $m,h$ bound the two exponent sets and let
$c=|A|\max(m,h)+1$. For $n\ge 2c+1$, each of the two pieces of a
length-$(n+1)$ word outside zero-based positions $c,c+1$ has at least
$c$ letters. Each piece contains at least $\max(m,h)+1$ copies of
some letter. Distinct frequent letters would give a forbidden Het
subword. With the same frequent letter on both sides, either intervening
letter differing from it would give a forbidden Hom subword. Thus the
two intervening letters agree throughout the longer promise.

Deleting position $c+1$ maps the longer promise injectively into the
shorter one, with inverse on its image given by copying position $c$.
A protocol for the shorter promise pulls back at the same depth by
reading the surviving coordinates. The exact minimum therefore
satisfies $h^{\mathrm{rd}}_L(n+1)\le h^{\mathrm{rd}}_L(n)$ throughout
the tail. A nonincreasing sequence of natural numbers is eventually
constant.

## Falsifier

A counterexample would be a subword-closed language over a finite
alphabet of at least two letters with both exponent sets finite and
with unequal recognition depths arbitrarily far along the sequence
of lengths. The result excludes that entire class.

## Evidence

The settling declaration is
`D5/S3/Observer/Budget/HussainRecognitionDepth.result`.
The source-tree criterion is connected to the frozen
`AdaptiveProtocol` through `source_exact_iff` and equality of the
minimum depths. The adjacent-coordinate step and the protocol transfer
are used in the proof of the source claim.

## Triage

- **Proved in Lean.** Every language in Theorem 1(c) has an eventually
  constant exact deterministic recognition depth.
- **Proved in Lean.** Eventual nonincrease applies whether the promises
  stay nonempty or become empty.
- A finite language has empty length promises beyond its maximum word
  length and then has depth zero by the empty-promise convention.
- The recognition conclusion is on promised inputs for each length.
  Membership queries have the entire length slice as their input domain.

## ASSUMED-UNVERIFIED

Literature coverage of citing work and versions beyond the inspected
source remains incomplete. The proof settles the statement in arXiv v1.
[Issue #33567](https://github.com/the-omega-institute/trureturing/issues/33567)
