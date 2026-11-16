---
slug: acls-reflection-complexity-c28
bibkey: allouche2025reflectioncomplexity
doi: 10.1007/s00224-025-10234-x
url: https://arxiv.org/abs/2406.09302v4
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28
---

# Bounded reflection differences for words of linear factor complexity

## Problem

Allouche, Campbell, Li, Shallit and Stipulanti, *The reflection complexity of
sequences over finite alphabets*, arXiv:2406.09302v4, Conjecture 28, p. 15:

> Let $\mathbf{x}$ be a sequence of at most linear factor complexity.
> Then $r_{\mathbf{x}}(n+1)-r_{\mathbf{x}}(n)$ is bounded for all $n\ge0$.

The bounded-difference assertion is **Proved** under the conventions of
[#24159](https://github.com/the-omega-institute/trureturing/issues/24159).
The source's subsequent automaticity sentence is outside this assertion.
Both delivered modules have generality G and utility none. The settling
module has admission basis open-problem-resolution (#24159; Proved); the
support module has admission basis escape-witness.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite alphabet | `claim` quantifies over every `A : Type` with `Fintype A` | Arbitrary finite alphabets, including the empty type; a word into it cannot exist. |
| One-sided sequence | Every function from natural positions to A | No recurrence, aperiodicity or reversal-closure premise. |
| Contiguous length-n factors | Frozen `MorseHedlund.wordFactorSet` | Zero-based positions preserve the factor sets and include the empty factor. |
| Reflection equivalence: v=u or v=u reversed | `AlloucheReflectionComplexitySupport.ReflectivelyEquivalent` | The literal disjunction, using `Fin.rev`. |
| Reflection complexity | `AlloucheReflectionComplexitySupport.reflectionComplexity` | Cardinality of the quotient of actual factors; reversed factors need not occur. |
| At most linear factor complexity | A natural C with $p_x(n)\le C(n+1)$ for all natural n | Enlarge an asymptotic linear bound and absorb the finitely many initial values. |
| Bounded consecutive differences for every n≥0 | `result : claim` | Subtraction is in the integers, followed by `Int.natAbs`; negative steps remain in scope. |
| Automaticity sentence | Outside `claim` | Generalized numeration requires the source's addable positional-numeration hypotheses. |

## Motivation

The conclusion applies to periodic words and words with transient prefixes
as well as recurrent aperiodic words. It establishes a uniform bound over
all factor lengths for each word satisfying the linear-growth premise.
The quotient counts occurring factors rather than a language assumed closed
under reversal.

## Gap

The source leaves the unrestricted bounded-difference assertion open.
Dvořáková and Pelantová, *Reflection on the Reflection Complexity*,
arXiv:2511.12358v1, Section 6; DOI 10.1007/s00224-026-10278-7, establishes
the reversal-closed case and restates the unrestricted assertion.
The literature screen recorded in #24159 found no unrestricted settlement
in its inspected scope. Literature completeness and priority are
ASSUMED-UNVERIFIED.

## Route

Write $L_n$ for the actual length-n factors and
$u_n=|L_n\cup L_n^R|$. Insert a fresh marker at the center of the bi-infinite
mirror of x. Its factor count is exactly $u_n+n$: unmarked factors are
lifts of the symmetrized language, and the n marked factors are disjoint
from them and from each other.

For the bi-infinite language, every fixed-offset crop is surjective.
Weighted factor graphs control the excess at an intermediate length using
two lengths with small increments. A cut estimate forces heavy edges to
return, and word overlap prevents two heavy outgoing edges. Interval
averaging under linear growth supplies the two lengths. This proves the
needed bi-infinite Cassaigne ingredient without taking a language theorem
as a hypothesis. Reflection-orbit counting and deletion of palindromic
loops transfer its bound to the original word.

## Falsifier

A finite alphabet and a one-sided word with linear factor complexity but
unbounded integer reflection differences contradict `claim`. A mismatch
between the quotient relation and source Definitions 1 or 3 would defeat
source fidelity. The statement uses the source relation restricted to
actual factors and does not assume that reversals occur.

## Evidence

`D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28.result`
proves the full bounded-difference assertion. Its elaborated proof consumes
`AlloucheReflectionComplexitySupport.mirrorFactorLinear`, the private
`Scalar.biinfinite_bounded_differences`, and
`AlloucheReflectionComplexitySupport.reflectionBoundOfMirrorBound`.
The axiom closure of every public declaration is contained in
{propext, Classical.choice, Quot.sound}.

The four-slot escape audit remains unfinished for `fiberSurplus`,
`mirrorFactorLinear`, `reflectionBoundOfMirrorBound` and `result`, under
[#29928](https://github.com/the-omega-institute/trureturing/issues/29928).
No declared_validated registration is claimed.

### Exact finite experiment

[Immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c9f5c96ca6c988190a2b67aaf38b4f3c42869877/docs/reports/allouche-reflection-complexity-c28).
The script is `docs/reports/allouche-reflection-complexity-c28/check.py`,
SHA-256 `a523f22f535caa2b4b4930fb354fe540013eb15e535f971cc301c44f0ac31b0d`.
Command executed on the exact script bytes extracted from that revision:
`python3 /Users/auric/.op-scratch/op/acls2406/stageb/check.py`, exit 0,
final line `ALL_CHECKS_OK`.

It checks 1,457 ultimately periodic presentations and 24,769 comparisons
at lengths $n=0,\ldots,16$: unary prefix lengths 0–3 and period lengths
1–5; binary prefix lengths 0–3 and period lengths 1–5; ternary prefix
lengths 0–2 and period lengths 1–3. There are 1,090 presentations lacking
reversal closure in the inspected range and 2,160 negative reflection
steps. The source Thue–Morse example is reproduced. These are exact finite
computations, separate from the universal proof.

## Triage

| Item | Status and evidence |
| --- | --- |
| Palindromic-loop inequality $q_n+P_{n+1}\le q_{n+1}+1$ without a linear premise | **Proved, kernel-checked:** private `AlloucheReflectionComplexitySupport.reflection_loop_count`; $P_n$ counts palindromes in the symmetrized language. |
| Full claim for arbitrary finite alphabets and one-sided words of linear factor complexity, including periodic words and transient prefixes | **Proved, kernel-checked:** `AlloucheReflectionComplexityConjecture28.result`. |
| Exact marked-mirror construction and the consumed Cassaigne ingredient | **Proved, kernel-checked:** private `AlloucheReflectionComplexitySupport.mirror_factor_decomposition`, `mirror_factor_card`, and `AlloucheReflectionComplexityConjecture28.Scalar.biinfinite_bounded_differences`; no language theorem remains a hypothesis of result. |
| Nonsharp scalar witness | **Proved by the proof's explicit witness:** private `Scalar.biinfinite_bounded_differences` chooses $D(C)=\max(9C,3C((3C+1)(24C+1)+6C+1))$; `result` applies it at $2C_{\rm source}+1$, and `reflectionBoundOfMirrorBound` chooses $B=D(2C_{\rm source}+1)+1$. This is proof-term witness information, not a separately exported bound theorem. |
| Pinned exact checker and source Thue–Morse example | **Computed:** the experiment entry above gives the immutable program, command, exit 0, SHA-256, and exact tested scope: 1,457 presentations, 24,769 comparisons, 1,090 without reversal closure, and 2,160 negative steps. |
| Sharpness or optimal growth in the linear coefficient | **Open:** no optimality or matching lower bound is established. |
| Automaticity and generalized numeration | **Open here:** outside the binding claim; no formal automaticity bridge is delivered. |
| General factorial-language theorem beyond bi-infinite realization | **Open here:** only the needed bi-infinite instance and general graph estimates are delivered. |

### What the settlement shows

The decisive mechanism is a linear-cost marked-mirror realization of reversal
symmetrization, followed by graph estimates and palindromic-loop deletion.
The loop inequality requires no growth assumption. The final theorem keeps
all one-sided words satisfying linear factor growth, so periodicity and
transient prefixes require no separate cases. The explicit scalar witness
supplies a finite, nonsharp coefficient-dependent bound.

The source's Theorem 30 already states a universal lower bound on reflection
differences; it is literature context, not on this module's dependency path.
The settlement supplies the unrestricted upper control needed for the
bounded-difference assertion. It does not alter hypotheses of the source's
other proved results. Automaticity consequences require their regularity
and numeration bridges, and are not additional kernel-checked conclusions
here.

## ASSUMED-UNVERIFIED

Global literature completeness, priority, the original journal subscription
full text, the later opacity journal full text, direct access to Cassaigne's
1996 primary paper, and author-index completeness remain unverified as
recorded in #24159. The later precise language statement is attested by
Leemann–Nagnibeda–Skripchenko–Veprev, arXiv:2402.15877v2, Lemma 2.14;
the delivered proof establishes the needed bi-infinite case directly.
Finite experiment results do not assert a uniform infinite-language theorem.
