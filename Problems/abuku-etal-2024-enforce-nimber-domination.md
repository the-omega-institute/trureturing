---
slug: abuku-etal-2024-enforce-nimber-domination
bibkey: abuku2024enforce
doi: 10.1007/s00182-024-00910-6
url: https://arxiv.org/abs/2311.01006v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/AbukuEnforceNimberDomination.result
---

# Ruleset domination does not imply nimber domination

## Problem

Abuku, Kimura, Kiya, Larsson, Saha, Suetsugu and Yamashita,
*Enforce and selective operators of combinatorial games*, arXiv:2311.01006v2,
Section 8, Problem 42, printed page 23 asks:

> If a ruleset dominates another, does it also ‘nimber dominate’ that ruleset? That is, does it follow that all nimbers of the combined ruleset are the same as those of the dominating ruleset?

The source is also published in *International Journal of Game Theory* 53,
1249–1273, DOI 10.1007/s00182-024-00910-6. The preregistration is
[issue #19251](https://github.com/the-omega-institute/trureturing/issues/19251).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Positions and option maps, Definition 2 | Arbitrary type `X` and `fA fB : X → Set X` | No finite-board assumption in `claim`. |
| Every play has a finite bound from its starting position, Definition 4 | `Short` quantifies over starts, bounds and sequences | The displayed source condition is used directly. |
| Union ruleset is short, Definition 10 | `JointlyShort fA fB` | Both option maps share the same position type. |
| Perfect-play outcomes, Definition 5 | `Outcome`, `IsOutcome fA OA` | P exactly when every option is N. |
| Opponent enforces one ruleset before the move, Definition 13 | `IsEnforceOutcome fA fB OE` | P exactly when at least one ruleset has only N options. |
| Domination, Definition 14 | Pointwise equality of `OE` and `OA` | Equality holds at every position. |
| Least excluded natural, Definition 28 | `mex s = sInf sᶜ` | This totalizes the source's finite-set mex; empty complement gives 0 by the Nat sInf convention. The witness uses only finite sets. |
| Ordinary nimbers, Definition 29 | `IsNimValue fA GA` | Mex of the ordinary option-value image. |
| Enforce nimbers, Definition 33 | `IsEnforceNimValue fA fB GE` | Mex of the intersection of the two option-value images. |
| All combined nimbers equal the dominating ruleset's nimbers, Problem 42 | `claim` concludes pointwise equality of `GE` and `GA` | `result` proves the negation of this universal implication. |

The four function parameters satisfy the source recursions; they introduce
no extra restriction on the refuting board. The witness uses three positions
and provides each of the four functions explicitly. No general uniqueness
or existence theorem for these recursions is claimed.

## Motivation

Outcome equality retains a zero/nonzero distinction but does not specify
positive nimber values. An intersection of option-value images can lose a
positive value while preserving whether zero is excluded.

## Gap

The conclusion refuted is Problem 42's universal implication. The unbounded
family proposed alongside the concrete witness is checked only on the finite
range below. Its unrestricted formulas and the strong-domination question
remain open here. Literature completeness is ASSUMED-UNVERIFIED.

## Route

On $X=\{0,1,2\}$ take $f_A=(\varnothing,\{0\},\{0,1\})$ and
$f_B=(\varnothing,\{0\},\{0\})$. Every option strictly decreases its index,
so every play in the union terminates. The outcome functions both equal
$(P,N,N)$, while the ordinary and enforce nimber functions are $(0,1,2)$
and $(0,1,1)$. Specializing `claim` at this board gives $1=2$ at position 2.

The private helper `mex_eq` applies Mathlib `csInf_eq_iff` to the complement
set. The finite recursions use it through `nim_a` and `nim_enforce`.
No D5 owner is imported and there are no direct frozen D5 dependencies.

## Falsifier

A proof of the universal `claim` contradicts the kernel-checked `result`.
The falsifying position is 2: both outcomes are N, but its enforce nimber
is 1 and its ordinary nimber is 2.

## Evidence

- Lean source: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.lean`.
- Full Lean namespace: `D5.S0.Certificates.Games.AbukuEnforceNimberDomination`.
- Settling theorem: `result`, proving `Not claim`.
- Blueprint source: `Blueprint/D5/S0/Certificates/Games/AbukuEnforceNimberDomination.scribe.cs`.
- Source note: `Library/Certificates/abuku2024enforce.md`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The reproducible checker is in
[trureturing-experiments, pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/bd14a1c66f56f5b37e21ff25c1799ca3dce6f793/docs/reports/abuku-etal-2024-enforce-nimber-domination).
Command: `python3 docs/reports/abuku-etal-2024-enforce-nimber-domination/check.py`
from that repository at commit `bd14a1c66f56f5b37e21ff25c1799ca3dce6f793`;
exit 0, `RESULT PASS`. Script SHA-256:
`419164f3171631abd6dc3cba2bd56af32a6cab071962c1bcb6e941f2cf8be46b`.
The checked local script has the same SHA-256 as the pinned Git blob.

The checker computes the three-position outcome and nimber arrays above.
For $d=3,\ldots,7$ and $N=2d,\ldots,59$, on $\{0,\ldots,N\}$ it checks
$f_A(n)=\{m:m+2\le n\}$ and $f_B(n)=\{dk:dk<n\}$, equality of the outcome
arrays, $G_A(n)=\lfloor n/2\rfloor$, and $G^E(n)=0$ for $n<2$ and
$G^E(n)=\lceil n/d\rceil$ otherwise. At each checked $n=2dr$ it verifies
the gap $(d-2)r$. It also enumerates pairs of decreasing option maps on
one- and two-position boards and finds no dominating pair with unequal
nimber arrays. The empty board has no position at which to differ;
relabelling any jointly short board with at most two positions puts its
union into the enumerated decreasing order.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Equal outcomes at every position coexist with a positive nimber mismatch at position 2. | Kernel-checked: `result`, using the private `jointly_short`, `outcome_a`, `outcome_enforce`, `nim_a` and `nim_enforce`. The constructed arrays agree on outcomes and differ on nimbers at 2. |
| The failure mechanism is loss of a positive option value in the intersection. | Explanation of the kernel-checked witness: A's option values at 2 are $\{0,1\}$, but the enforce intersection is $\{0\}$. Their mex values are 2 and 1. Both outcomes are N. |
| The proposed family has domination, both displayed formulas and gap $(d-2)r$ for $d=3,\ldots,7$, $N=2d,\ldots,59$. | Computed only: the pinned experiment above, exit 0. No Lean theorem of the uniform family is delivered. |
| There is no counterexample on at most two positions. | Computed for every decreasing option-map pair on one and two positions by the pinned checker, exit 0; the relabelling and empty-board justification are given above. No Lean minimality theorem is delivered. |
| The unrestricted family formulas and an unbounded nimber gap. | Open here: the finite checks do not establish a uniform theorem for all $d\ge3$, $N\ge2d$ or unbounded $r$. |
| Whether strong domination, Definition 24, implies nimber domination. | Open here: no theorem or experiment resolves the quantification over every jointly short auxiliary ruleset C. |

The nearest surviving statements are the equal outcome arrays and the
source's outcome-level domination results: `result` asserts only a failure
of the proposed lifting to nimbers. It does not negate an outcome-level
theorem. No other result of the source is claimed to depend on Problem 42.

## ASSUMED-UNVERIFIED

Literature completeness and priority are ASSUMED-UNVERIFIED. The literature
screen recorded in #19251 covers arXiv:2311.01006v2, the publisher record,
2405.20054v2, 2511.14468, 2605.29918 and Morisawa's
DOI 10.1007/s00182-026-00991-5. It reports no answer in those sources.
Citation discovery is incomplete: the reported OpenAlex cited-by count was
zero and Semantic Scholar was rate-limited. The Odawara thesis and the
enforce-operation talks remain unread. These are source-screen readings
attributed to the preregistration's producers, not an exhaustive search by
the implementation seat.
