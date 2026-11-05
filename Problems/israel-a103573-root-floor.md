---
slug: israel-a103573-root-floor
bibkey: israel2026a103573
doi: null
url: https://oeis.org/A103573/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/IsraelA103573RootFloor.result
---

# Israel's A103573 root-difference conjecture

## Problem

This dossier anchors exactly the ceiling conjecture in OEIS A103573 revision 13,
FORMULA, attributed to Robert Israel; Ray G. Opao submitted the sequence.
The NAME states: "a(n) is the least integer such that
floor(a(n)^(1/2)-a(n)^(1/3)) = n."
The FORMULA conjectures that a(n) is either ceiling(T(n)) or 1+ceiling(T(n)), where

T(n)=n^2+2*n^(5/3)+(7/3)*n^(4/3)+2*n+(110/81)*n^(2/3)+(182/243)*n^(1/3).

For every nonnegative integer n, a(n) is the least nonnegative integer k whose
ordinary integer floor of sqrt(k)-k^(1/3) equals n. All powers are real powers
of nonnegative bases, with ordinary nonnegative real square and cube roots.
The domain follows the source's real-root convention, nonn keyword and program
starting candidates at zero; OFFSET starts at zero. Source sequence existence
and leastness are included, and the two-ceiling assertion applies to every such
sequence at every n>=0. No positive-index or eventual restriction replaces the
target. Floor and ceiling are integer valued, also for a negative root difference.

| Source clause | Lean definition or declaration |
| --- | --- |
| Ordinary real square and cube roots | `f` |
| Original rational real powers and coefficients | `T` |
| Every natural index, integer floor and least natural candidate | `IsSourceSequence` |
| Source existence and every source sequence's two-ceiling formula | `claim`, `result` |
| Zero index | `candidate`, zero branch |

## Motivation

A uniform rounding formula connects the sequence's least-integer definition to
an explicit real approximation. Existence and leastness must hold at the zero
index as well as positive indices. The formal target is
`D5/S3/ArithSums/IsraelA103573RootFloor.result`; preregistration is
[issue #26800](https://github.com/the-omega-institute/trureturing/issues/26800).

## Gap

The registered classification is Tier 1, a small named OEIS conjecture with an
algebraic threshold route. The source presents a conjecture rather than a proof;
its revision-13 attribution and statement are in
`Library/Asymptotics/israel2026a103573.md`.
The accepted bounded screen covers primary/internal source, all 13 displayed
history revisions, MathDB, private-inclusive repository, pinned Mathlib and
admissible third-party qualification. No whole answer was authenticated within
those checked scopes. Prior art remains partial: these readings do not certify
world-wide openness, novelty or exclusive ownership. The unsuccessful global
query supplies no negative evidence and is not a completed literature check.

## Route

For n>0, q(t)=t^3-t^2 is strictly increasing on t>=1. The intermediate value
theorem supplies a threshold r=t^6 with sqrt(r)-r^(1/3)=n. For
P_n(X)=X*(X+3*n^2)^2-((3*n+1)*X+n^3)^2, exact polynomial expansion gives
P_n(T(n))<0<P_n(T(n)+1) through positive-coefficient residual factors. The
discarded square-comparison factor is strictly positive, preserving the root
branch and giving T(n)<r<T(n)+1. The least admissible natural candidate is
ceil(r): its root difference lies in [n,n+1), while every smaller nonnegative
integer has root difference below n. Ceiling monotonicity gives the two stated
possibilities. At n=0 the least candidate and T(0) are both zero.

## Falsifier

A nonnegative index with no least admissible natural candidate, or a source
sequence and index whose value is neither ceil(T(n)) nor ceil(T(n))+1, refutes
the full target. A changed floor interpretation, omitted zero case, extraneous
root branch or added hypothesis invalidates source fidelity. A published whole
answer defeats a new-resolution claim and requires reuse with zero new solve
credit; bounded search failure cannot rule out such an answer.

## Evidence

Existing selected Lean evidence covers the unchanged complete `claim` and
`result`: source existence, leastness, n=0 and both original ceiling values.
The accepted scoped report records only Classical.choice, Quot.sound and
propext, with no sorryAx or new/private axiom. Its scope is the selected module
and imports, not whole-repository health or required CI. Pinned Mathlib root,
power, intermediate-value, ordered-ring and integer floor/ceiling results are
reused. Source evidence is cited in `Library/Asymptotics/israel2026a103573.md`.

The declaration disclosure is `proof_shape: bind-only` throughout. No helper
supplies an escape witness or separate solve credit. Actual live consumers
(all names in the target module) are:

| Declaration | Actual live consumer |
| --- | --- |
| `q_mono` | `f_mono` |
| `f_repr` | `f_mono` |
| `f_mono` | `threshold_bracket`, `positive_candidate` |
| `p_sign` | `T_bracket` |
| `poly_bracket` | `T_bracket` |
| `T_normalize` | `T_bracket` |
| `T_bracket` | `threshold_bracket` |
| `threshold` | `positive_candidate` |
| `threshold_bracket` | `positive_candidate` |
| `positive_candidate` | `candidate` |
| `candidate` | `result` |
| `result` | Complete external assertion; designated result, not a helper |

The intended admission basis for `result` is `open-problem-resolution`, linked
to preregistration #26800. Helpers supply organization only. The module retains
`utility: none`. Condition-(b) disclosure must also appear in any later PR;
this dossier does not assert that a PR exists.

## Triage

Proved in existing selected Lean evidence: source existence and leastness at
every n>=0, and the original two-ceiling assertion for every source sequence.
The mechanism is the threshold bracket and monotonicity, with zero handled
separately. Choosing which ceiling alternative holds, sharper uniform brackets
and related root-difference families remain unproved here; no extension or new
declaration is claimed. The cited source supplies no downstream theorem whose
dependence is independently settled here. This metadata asserts no freeze,
final admission, publication, novelty certification or solved-problem count.

## ASSUMED-UNVERIFIED

Prior-art coverage remains partial, with no global absence certificate. No
corresponding theory was found and no atom was encountered in the bounded
qualified scope, without asserting absence under arbitrary renaming. Any later
authorized freeze uses canonical deposit-uncovered for the actual GID, without
forced theory ingestion or fabricated consumers.

Four-slot source registration remains unfinished under
[issue #26804](https://github.com/the-omega-institute/trureturing/issues/26804),
using the CLAUDE.md section 3.9 linked-issue exception. Complete source
reconstruction, lawful enrolled-template application, the statement/Law bridge,
actual-positive law, whole-family variation and sensitivity, actual observational
dependence, and compiled mirror/current binding evidence remain missing. A state
containing only k leaves ceil(T(n)) constant in that state and cannot establish
observational dependence; a faithful larger state/source construction remains
unfinished. No API impossibility or judge defect is asserted, and no
`declared_validated` registration is claimed. Required checks and final admission
remain separate obligations.
