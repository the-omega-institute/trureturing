---
slug: oeis-a378495-adjacent-difference
bibkey: kagey2024a378495
doi: null
url: https://oeis.org/A378495
triage: theorem
motivation_gids:
  - D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution_mul
---

# The literal adjacent difference of OEIS A378495

## Problem

OEIS A378495, revision 70, FORMULA, states verbatim:

> Conjecture: T(n,n-1) - T(n,n-2) = abs(A238474(n-4)) for n >= 4.

On the source-agreeing columns $2\le k\le n$, $T(n,k)$ counts derangements
of $S_n$ having no $k$-cycle; the source explicitly sets $T(n,1)=0$.
The triangle has offset `1,5`. The dependent A238474 entry, revision 15,
has offset `0,1` and formula $b(m)=(-1)^m(m+3)!/(2(m+1))$ for every
natural $m$. This is interpreted in $\mathbb Q$, with rational ordinary
subtraction between cast cardinalities and rational division in $b$.

### Statement echo

| Source clause | Exact formal counterpart |
| --- | --- |
| Every $n\ge4$ | `claim` quantifies over every `n : Nat` with `4 <= n` |
| Actual derangements with no $k$-cycle | Imported `TerminalDifference.T`, using permutations of `Fin n`, no fixed points, and cycle-factor support sizes |
| Ordinary difference of adjacent columns | `(T n (n-1) : Q) - (T n (n-2) : Q)` |
| Zero-based A238474 | `b (m : Nat) : Q` uses the source factorial quotient |
| Literal source shift $n-4$ | Exactly `abs (b (n-4))`, with natural subtraction |
| Universal assertion is false | `theorem result : Not claim`, a closed negation of the literal `Prop` definition |

## Motivation

The tier-one external question is preregistered separately in
[#23900](https://github.com/the-omega-institute/trureturing/issues/23900#issuecomment-6508953571).
It is Peter Kagey's revision-59 formula from 2024. Its interpretation
depends on Wolfdieter Lang's 2014 zero-based sequence, whose formula and
offset are recorded in the [source note](../Library/FiniteGroups/lang2014a238474.md).
The frozen motivation theorem is a related application of permutation
cycle-type cardinalities, not a proof dependency or a substitute result.

## Gap

The exact original assertion is refuted by
`D5.S3.Combinatorics.Derangements.AdjacentDifferenceRefutation.result`.
The [A378495 note](../Library/FiniteGroups/kagey2024a378495.md) records
the bounded fixed-pin supplier and literature search. Kallat v1,
section 9.2 and supplementary `sec:open`, leaves this stronger identity
outside its proved results. OpenAlex search and Semantic Scholar
HTTP 429 gaps preclude a global literature-completeness claim.
The counterexample does not require assuming that the formula is novel.

## Route

Use $n=5$. A derangement on five labels cannot have a 4-cycle, since
the unused label would be fixed. Thus `excluded 5 4` is empty. The actual
permutations excluded by a 3-cycle have cycle type $\{3,2\}$ and number
$5!/(2\cdot3)=20$. The two complementary-count equalities on the same
finite set of derangements give $T(5,4)=T(5,3)+20$. After rational casts,
$T(5,4)-T(5,3)=20$.

The unchanged source shift gives $b(5-4)=b(1)=-6$, so the proposed right
side is 6. Since $20\ne6$ and $5\ge4$, the universal assertion fails.
The proof uses exact cardinality identities, not an assumed triangle
formula, an unexplained table, or a search over a finite range.

## Falsifier

The equality at five would force $20=6$. To challenge the refutation's
source fidelity on its relevant columns, one must identify a different
source no-$k$-cycle convention for $k\ge2$ or sequence offset; both are
fixed explicitly above. The separately disclosed $k=1$ source exception is
outside the $n=5$ columns $4$ and $3$. Replacing $n-4$
by another shift defines another question and cannot repair the original
assertion's counterexample.

## Evidence

The independent scientific terminal is
[6510325154](https://github.com/the-omega-institute/trureturing/issues/23900#issuecomment-6510325154).
It refutes exactly the original literal statement. Its result statement
identity is `sha256:38f5f82bc3c0255dc8908fb63b1c0200d69e76147a4b223e00f6ffd41fd925b3`.
The definition `claim` has literal compiled type `Prop`, and `result`
has literal compiled type `Not claim`. The accepted axiom closure is
contained in `Classical.choice`, `Quot.sound`, `propext`.
The display formulas are typed authored presentations of the exact
source, with complete mathematical prose. The projector reports
`missing` for the unfrozen declarations; no kernel-derived formula
projection is claimed. Independent fidelity review remains required.

### Declaration form, admission and utility

Names below are relative to `AdjacentDifferenceRefutation`.

| Declaration | proof_shape | Live consumer or independent question |
| --- | --- | --- |
| `b` | definition; not applicable | `claim`, `result` |
| `claim` | definition; not applicable | The closed negation `result` |
| `result` | bind-only | The literal external question preregistered in #23900 |

There are no new helper theorems and no escape witness. The inline proof
uses pinned cycle-type facts, the actual `TerminalDifference`
partition/count suppliers, logical decomposition and exact arithmetic.
The intended admission basis is `open-problem-resolution`. Utility is
`certified-instance`, with `basis=refutes` referring to the exact local
`claim` and the designated `result`. The definitions support that same
refutation and introduce no independent positive instance. Generality
is `I`, reflecting the concrete five-label witness.

The source and its supplier are unfrozen. Independent pre-freeze review,
canonical doors and the final typed Refuted claim remain pending.
No existing frozen project declaration on the live proof path is claimed.
The designated refutation result is exempt from four-slot registration;
`b` and `claim` are definitions, not additional audit targets. The nine
supplier theorems retain their unfinished
[section 3.9 audit exception](https://github.com/the-omega-institute/trureturing/issues/23899#issuecomment-6509479812).
No Reg registration or `declared_validated` status is claimed for them.

The separate scientific readings recorded in
[6510337040](https://github.com/the-omega-institute/trureturing/issues/23900#issuecomment-6510337040)
are $X=0,Y=1,Z=0$, one `p5` unit, score coverage 1, mode coverage 1,
and zero missing counts. These readings concern this one event; they
are not delivery, calibration, research-value or novel-general-discovery
credit. The first event's readings remain unproduced under its unchanged
unsupported historical fence, and are not replaced by these values.

## Triage

### What the settlement shows

- **Proved in Lean:** the exact negation of the original universal claim,
  from the actual five-label difference $20$ and absolute sequence value $6$.
- **Computed exactly within the proof:** the arithmetic specialization
  at five and $b(1)=-6$; no positive finite table establishes a universal law.
- **Mechanism:** a 4-cycle leaves a fixed point, whereas cycle type
  $(3,2)$ has twenty realizations. The zero offset fixes the comparison
  to $b(1)$.
- **Open:** a corrected shift, restricted-range replacement or neighboring
  identity is not established here. In particular no $n-3$ replacement
  is claimed proved.
- **Unaffected:** the separate original terminal formula has its own
  [proof dossier](oeis-a378495-terminal-difference.md). No failure of
  Kallat's other results or of the whole paper is inferred.
- **Boundary:** admission and publication remain pending; no delivery
  or KPI is claimed from the scientific settlement or readout.

## ASSUMED-UNVERIFIED

Global novelty, priority and literature completeness are unestablished,
including the named rate-limited search endpoints. Historical producer
times are recorded assertions with unchanged server evidence, not newly
recovered process telemetry. Pre-mathematics full native closure ordering
remains unestablished. The supplier's audit is unfinished and the first
event's readings are unproduced. No final CI, freeze or publication
completion is asserted.
