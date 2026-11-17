---
slug: a155200-binaryvaluation
bibkey: hanna2009a155200
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/LocalDold/HannaA155200BinaryValuation.result
url: https://oeis.org/A155200/internal
---

# Hanna's A155200 exact binary valuation

## Problem

Paul D. Hanna's [OEIS A155200](https://oeis.org/A155200/internal), revision #39,
defines the ordinary coefficients by
$A(x)=\exp(\sum_{k\ge1}2^{k^2}x^k/k)=\sum_{n\ge0}a(n)x^n$ and states:

> Conjecture: highest exponent of 2 dividing a(n) = A000120(n) = number of 1's in binary expansion of n, so that a(n)/2^A000120(n) is odd for n >= 0. - Paul D. Hanna, Sep 01 2009

The target is [preregistration #21398](https://github.com/the-omega-institute/trureturing/issues/21398).
Write $s_2(n)$ for the sum of the binary digits. The settlement proves that for
every natural $n$, including zero, there exists an odd integer $z$ with
$a(n)=2^{s_2(n)}z$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Formal exponential of the displayed sum | `claim` | The generating expression is inlined literally over the rationals; its exponent has zero constant coefficient. |
| Ordinary coefficient $a(n)$ | `PowerSeries.coeff` in `claim` | No factorial is built into coefficient extraction. |
| All $n\ge0$ | The natural-number quantifier in `claim` | Includes zero. |
| A000120 is the binary ones count | `Nat.digits 2 n` followed by `List.sum` | The empty digit list at zero sums to zero. |
| The quotient is an odd integer | The integer existential and `Odd` in `claim` | Gives both exact divisibility and failure of the next power of two to divide. |
| No extra source assumptions | `result : claim` | No integrality or recurrence premise is added to the public assertion. |
| General rational sequence and recurrence in the private normalization helper | `normalized_integral_mod_four` | An internal proof generalization, instantiated with the literal coefficients. |

The dropped or weakened source-clause set is empty. The source expressions
stay in `claim`; the proof uses the existing `exponentialSum` and
`logarithmicInput` through their definitional correspondence, without new
forwarding definitions.

## Motivation

The settling GID is `D5/S3/Arith/LocalDold/HannaA155200BinaryValuation.result`.
Its admission basis is `open-problem-resolution (#21398; Proved)`, generality
is `I`, and utility is `none`. All retained constructions and conclusions
are symbolic and unbounded in the natural index.

## Gap

Integrality alone does not give the exact power of two. The additional
information is that $b(n)=n!a(n)/2^n$ is an integer congruent to one modulo
four. The denominator contributed by the factorial is then removed using
its binary digit-sum identity and coprime divisibility cancellation.

## Route

`geometric_exponential_integral` proves integrality for the geometric input
using the imported `CompositionalIterateCongruence.geometric_inverse`.
`HannaDiagonalGhostPowerIntegrality.result` transfers it to the square-index
weights. Its published `exponential_sum_constant` and
`exponential_sum_equation` give the initial value and differential equation.
Coefficient extraction gives the recurrence used by
`normalized_integral_mod_four`. Strong induction supplies the normalized
integer witnesses. The zero-index term preserves the residue; all remaining
terms contain $2^{k(k+1)}$ with $k\ge1$, hence a factor of four.
`odd_quotient_of_integral_normalization` uses the published
`BalaA361034Parity.binary_factorial_balance` and coprime cancellation.
The public `result` combines these statements for the literal exponential.

## Falsifier

A natural index for which the literal coefficient has no odd integer
quotient by $2^{s_2(n)}$ would negate `claim`. The proof covers every natural
index rather than a truncation. Analytic convergence is not assumed.

## Evidence

The Lean module and its Blueprint Scribe provide the all-index assertion.
The axiom closure of every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`.

### Exact-arithmetic experiment

The experiment is in
[trureturing-experiments at 31b29e657daeb7e0d4800b5877874738e89cef6c](https://github.com/the-omega-institute/trureturing-experiments/tree/31b29e657daeb7e0d4800b5877874738e89cef6c/docs/reports/oeis-a155200-hanna-binary-valuation).
The verified script is `check.py`, SHA-256
`322cb16ec53db08c8ce2a0dc2e89dadbea5f2f0f966f302639b10067eaa6893b`.
Command `python3 /Users/auric/.op-scratch/op/a155200/stageb/check-experiment.py`
exits 0. That local file is byte-identical to the pinned script. The source
prefix agrees at indices 0–13, an independent rational exponential expansion
agrees through degree 24, and integrality, exact valuation, odd quotient,
normalization modulo four and the factorial identity agree at indices 0–128.
These computations do not extend the scope of the kernel proof.

The additional command
`python3 /Users/auric/.op-scratch/op/a155200/stageb/neighbor-mod-eight.py`
exits 0 and verifies the modulo-eight formula below at all 129 indices 0–128,
using the pinned script's `normalized_coefficients` function. Its SHA-256 is
`7435269612794af842b89c48b49231d13839b278bf7c5554b71e5ebf2467e032`.
This additional program has no verified immutable experiments-repository
revision; its publication is unverified. No experiment program is included
in this repository.

### Literature

The primary source is the OEIS comment, not a conjecture in an arXiv paper.
Fried, [arXiv:2607.24832v1](https://arxiv.org/abs/2607.24832v1), Theorem 43,
proves the integrality background. The weighted-permutation recurrence and
factorial valuation identity are prior results. The scoped literature
screen and its unread-source boundaries are given in #21398.

Su Lien-Hung, *Exact p-Adic Arithmetic of Weighted Exponential Series and
Divisor-Sum Euler Products*, [version 1, DOI 10.5281/zenodo.23940708](https://doi.org/10.5281/zenodo.23940708),
Theorem 3.1, independently proves the A155200 valuation and a broader
positive-base family using weighted cycles and a unique least valuation.
The record was created 2026-11-04T09:06Z; #21398 was preregistered
2026-10-25T03:04:16Z. The theorem and its proof have been read. This
settlement makes no claim of an unpublished or globally novel mathematical
argument.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| A155200 is a 2-adic unit after removing $2^n/n!$; integrality and the factorial digit-sum identity give the exact quotient. | Proved; kernel-checked `result`, using private `normalized_integral_mod_four` and `odd_quotient_of_integral_normalization`. | For every natural $n$, $b(n)$ is an integer congruent to one modulo four, and $a(n)=2^{s_2(n)}z$ for an odd integer $z$. |
| Normalization for any rational sequence with the exact recurrence and initial value; integrality for the literal exponential is separate. | Proved; kernel-checked private `normalized_integral_mod_four`, and `result` for its application and coefficient integrality. | The helper quantifies over every rational sequence satisfying the displayed recurrence and $f(0)=1$; it does not assume integral coefficients. |
| $b(n)\bmod8=(1+4\lfloor n/2\rfloor)\bmod8$ through $n=128$. | Computed; exact arithmetic, command and SHA-256 in Evidence. | Verified only for $0\le n\le128$ by the additional local program; its immutable publication is unverified. No all-index modulo-eight Lean theorem is delivered. |
| Nonzero integer $q$ and prime $p\mid q$: $v_p(a_q(n))=nv_p(q)-v_p(n!)$. | Open; no general-$q$ Lean theorem in this delivery. | Su's Theorem 3.1 proves the positive-base family $q\ge2$, including more general powers. The full signed-base extension and a Lean generalization remain outside this settlement. |

The decisive invariant is the residue of the normalized recurrence. The
normalization helper extends to every rational sequence with that recurrence
and initial value, while integrality is established separately for the
source exponential. No source theorem identified in the literature screen
depends on the conjectured valuation as an unproved hypothesis.

The escape audit of `result`, the two published exponential-sum lemmas and
the published factorial identity is unfinished at
[issue #23611](https://github.com/the-omega-institute/trureturing/issues/23611).
No complete four-slot registration is claimed.

## ASSUMED-UNVERIFIED

- Literature-screen completeness, including unread sources and incomplete citation indexes, is `ASSUMED-UNVERIFIED`; the negative search results concern only the recorded scopes.
- The modulo-eight computation's additional program has not been verified at an immutable experiments-repository revision.
- The general nonzero-integer-base valuation theorem is not formalized here.
- The four-slot audit lacks the theorem-specific realization, reconstruction and sensitivity evidence listed in #23611.
