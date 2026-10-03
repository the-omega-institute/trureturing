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

- **已证 — odd-index mechanism.** Within `result`, `odd_coprime`
  establishes that `P(m)` is coprime to every `Q(j)` when `m` is odd.
  Companion oddness and `P(m)%2=m%2` force any index dividing either
  odd partial-sum factorization to be odd. Coprimality then forces
  `P(m)=1`, and strict growth forces the positive index to be one.
- **已证 — compression and growth.** Within `result`, `compress`
  gives `A|2BC => A|2*gcd(A,B)*gcd(A,C)`. Strong divisibility turns
  the latter gcds into Pell terms at `d=gcd(m,r)` and `e=gcd(m,s)`.
  If `m` exceeds the proposed maximum, these are positive proper
  divisors of `m`. For consecutive `r,s`, their coprimality gives
  `d+e<m`, hence `0<2P(d)P(e)<=P(d+e)<P(m)`. In the square branch,
  `2d<=m`; strict growth handles `2d<m`, and `Q(d)>P(d)` with
  `d>=2` handles `2d=m`, giving `0<2P(d)^2<P(m)`. A positive
  multiple of `P(m)` cannot be smaller than `P(m)`, excluding every
  larger dividing index.
- **已证 — sharp bounds.** All four values are exact maxima, not
  merely upper bounds: each `IsGreatest` clause of `result` includes
  positivity and divisibility at the stated index as well as the
  bound on every other positive dividing index.
- **已算 — zero-index boundary.** The latter two classes require
  `k>=1`. At `k=0`, `S(0)=0` is divisible by every `P(j)` with
  `j>=1`, so there is no greatest dividing index. The integer index
  `4k-1` is then `-1`, outside the sum's domain; Lean's natural
  subtraction truncates it to zero and does not extend that domain.
- **已算 — square-branch boundary.** The local `square_bound`
  requires `r>=2`. Replacing this with `r>=1` fails at `r=1,m=2`:
  `P(1)=1`, `P(2)=2`, and `P(2)|2P(1)^2=2`, although `2>1`.
- **已算(符号代入与原文依赖核对) — source dependency check.** In arXiv:2409.01296v1
  [Section 4.5](https://arxiv.org/html/2409.01296v1#S4.SS5),
  Theorem 19 uses the identities `S(4k)=2P(2k)P(2k+1)` and
  `S(4k-1)=2P(2k)^2`. Substituting `n = 4k` and `m = 2k + 1`
  supplies the common multiplier `2P(2k)` at adjacent sum and
  term indices: `S(n-1)=2P(2k)P(m-1)` and
  `S(n)=2P(2k)P(m)`. For `k = 1`, these are
  `S(3) = 8 = 4P(2)` and `S(4) = 20 = 4P(3)`. Theorem 19 then uses
  [Theorem 13](https://arxiv.org/html/2409.01296v1#Thmtheorem13)'s
  transfer to sequences with the same recurrence. Its proof does
  not require Conjecture 18's maximality. Settling the conjecture
  proves the maximum suggested by Table 8; it does not change
  Theorem 19's hypotheses or conclusion. This is a source-dependency
  check, not an additional Lean formalization of Theorem 19.
- **未决 — neighbouring recurrences.** A greatest-index
  classification for `x(n+2)=a*x(n+1)+x(n)`, with `x(0)=0,x(1)=1`
  and varying `a`, is not established here. The proof uses the
  companion's oddness and `P(m)%2=m%2` for its odd-sum branch,
  and the coefficient-2 addition, norm and partial-sum identities
  for compression and growth. These properties are established
  for the Pell recurrence; changing `a` requires appropriate
  companion identities, parity conditions and growth estimates.
  Theorem 19 transfers a sum identity while keeping coefficient 2;
  it supplies no maximum-index classification for varying `a`.
  Any new candidate requires separate preregistration, proof-shape
  and admission review, utility assessment and literature checks.
  This analysis introduces no new Lean declaration and does not
  extend this conjecture's resolution basis to another problem.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`; Bradie 2010 full text
and literature outside the searched indices remain unchecked. Lean
checks the exact formal theorem, while correspondence with the source
and proof-shape classification remain semantic review judgments. The
resolution claim does not establish repository merge or external
publication priority.
