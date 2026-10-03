---
slug: byrapuram-pell-partial-sum-max-index
bibkey: byrapuram2024pellpartialsums
doi: 10.1080/00150517.2025.2556152
url: https://arxiv.org/html/2409.01296v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/PellPartialSumMaxIndex
---

# Greatest Pell indices dividing initial partial sums

## Problem

Byrapuram et al., *Fibonacci Partial Sums Tricks*, arXiv:2409.01296v1,
Section 4.5, states verbatim:

> **Conjecture 18.** For the Pell sequence, we have
> m^P_{4k+1}=m^P_{4k+2}=1, m^P_{4k-1}=2k, and m^P_{4k}=2k+1.

Here `P(0)=0`, `P(1)=1`, `P(n+2)=2P(n+1)+P(n)`, and
`S(n)=P(1)+...+P(n)`. For positive `n`, `m_n^P` is the greatest
positive `j` satisfying `P(j)|S(n)`. The first two equalities hold for
every natural `k`; the latter two hold for every `k>=1`.
The formal predicate is `IsGreatest {j | 1<=j and P(j)|S(n)} m`, so
divisibility, positivity of the selected index, and maximality are all
part of each clause.

## Motivation

Issue #12462 fixes this Tier 1 external named conjecture, its literal
source, full quantifiers, proposed resolution and bounded literature
check before the Lean probe. It is a preregistration locator rather
than proof evidence.

## Gap

The source still labels the statement Conjecture 18. The bounded check
in #12462 covers the arXiv version, journal index, author discussion,
MathDB, Falcón Santana–Díaz-Barrero 2006 and Anand et al.
arXiv:2407.12868v2. The additional check finds arXiv v1 as the current
API entry and zero citing works in OpenAlex's index for W4402954534.
GitHub Lean-code queries for `Pell`, `Pell gcd`, `StrongDivisibility`
and the paper's arXiv identifier found no declaration resolving this
partial-sum maximum. Pinned Mathlib supplies natural-number gcd,
coprimality and strong-divisibility interfaces, but no Pell-number
instance for this recurrence. `Pell.xn` and `Pell.yn` describe different
Pell-equation solution sequences.

Bradie 2010 remains a full-text gap. Its accessible bibliographic
abstract discusses sums, squares and divisibility; it does not state
the greatest-index conclusion. No prior resolution was found in the
searched scope. The bounded search does not establish global novelty.

## Route

Reuse the Pell and companion definitions `P`, `Q` and their coupled
recurrence, same-index coprimality and companion oddness. The addition
formulas and the alternating norm identity give
`S(4k+1)=Q(2k+1)^2`, `S(4k+2)=Q(2k+1)Q(2k+2)`,
`S(4k-1)=2P(2k)^2` and `S(4k)=2P(2k)P(2k+1)`.
Euclidean gcd induction gives `gcd(P(a),P(b))=P(gcd(a,b))`.
For odd `m`, every common divisor of `P(m)` and `Q(j)` divides
`P(gcd(m,2j))=P(gcd(m,j))`, hence divides `P(j)`; coprimality with
`Q(j)` makes it one. Since the first two sums are odd, their dividing
Pell index is odd; coprimality makes its Pell value one and strict
growth makes its index one.

For the latter two classes, use the existing natural-number gcd
divisibility rules to deduce
`P(m)|2P(gcd(m,r))P(gcd(m,s))`. If `r=s` and `m>r>=2`, the gcd
index `d` satisfies `2d<=m`. The product is below `P(m)` by strict
growth when `2d<m`, and by `Q(d)>P(d)` when `2d=m`; the latter case
has `d>=2`. If `s=r+1` and `m>r+1`, the two gcd indices are proper
divisors of `m`, each at most `m/2`. Their coprimality makes their sum
strictly less than `m`. The addition formula gives
`2P(d)P(e)<=P(d+e)<P(m)`. The positive compressed divisor therefore
cannot be a multiple of `P(m)`. The displayed partial-sum factors
provide the claimed indices themselves.

## Falsifier

A positive dividing index larger than any displayed maximum would
refute the claim. Incorrect initial values, indexing a sum from one
past the endpoint, or including `k=0` in either latter clause would
break source fidelity. Checking finitely many sums cannot prove the
all-index statement.

## Evidence

`D5/S1/Recurrence/PellPartialSumMaxIndex.lean` defines `partialSum`
using `range(n+1)` and the canonical Pell `P`; its zero term vanishes.
The sole public theorem `result` contains all four `IsGreatest`
clauses. Every auxiliary fact is inside this proof. The formal result
is checked by the Lean kernel, with no `sorry`, new axiom, or native
decision procedure. The Scribe theorem binds the result to this
dossier using `OpenProblemResolutionClaim(Proved)`. Frozen publication
of that binding is a separate boundary.

## Triage

`theorem`; Tier 1 external named conjecture; resolution `proved`;
`admission_basis: open-problem-resolution`; `proof_shape: bind-only`.
The proof uses the frozen coupled recurrence, coprimality and oddness,
natural-number and Euclidean induction, existing gcd divisibility
theorems, finite parity branches, and arithmetic normalization. The
induction bases and steps close within those operations. No independent
escape witness is claimed. This is an unbounded general theorem with
`utility: none`, rather than a finite enumeration or certified instance.
There is no digestion atom or coverage edge.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`; Bradie 2010 full text
and literature outside the searched indices remain unchecked. Lean
checks the exact formal theorem, while correspondence with the source
and proof-shape classification remain semantic review judgments. The
resolution claim does not establish repository merge or external
publication priority.
