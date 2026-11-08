---
slug: crim-question-one-four-parts
bibkey: basic2026crim
doi: 10.48550/arXiv.2606.16828
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Games/CrimFourPartClassification.result
url: https://arxiv.org/abs/2606.16828v1
---

# Losing four-part positions in CRIM

## Problem

Bašić, Gottlieb and Krnc, *CRIM: A Natural Game on Integer Partitions*,
arXiv:2606.16828v1, Section 5, Question 1, printed p. 17 asks:

> Which partitions consisting of four parts are losing?

For every $a\ge b\ge c\ge d\ge1$, the answer is $G([a,b,c,d])=0$
if and only if $a$ is even and at least one of the following holds:

- $d\ge2$ and $b,c$ are not both odd;
- $d=c=1$ and either $b$ is even or $b=1$;
- $d=1$, $c\ge2$ and $b$ is odd;
- $d=1$, $c=2$ and either $b\ge3$ or $a=2$.

The alternatives may overlap. There is no upper bound on any part.
The formula is the answer preregistered in #23809; the source asks the
classification question and does not print this formula.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| Four positive parts in decreasing order | Natural parameters with $1\le d\le c\le b\le a$ in `claim` |
| Row or column deletion in normal-play CRIM | The original `CrimGrundyRefutation.moves` and `grundy` |
| Losing positions | Grundy value zero |
| Complete classification | The equivalence and all four alternatives in `claim`, proved by `result` |
| No size restriction | All four parameters are universally quantified without an upper bound |

Only the private proof uses sorted nonnegative quadruples with zeros removed;
the public statement retains exactly four positive parts. Remainders have
positive divisor two. Natural subtraction in the private move descriptions
is guarded by existence of the deleted column.

## Motivation

The classification gives a decision rule and a winning move to a losing
follower for every winning position with at most four rows. It reuses the
existing list-based CRIM move graph and well-founded Grundy evaluator.
The source's two- and three-row results motivate the four-row question.

## Gap

The result determines zero versus nonzero Grundy values. It does not classify
arbitrary positions with five or more rows or determine general positive
Grundy values as asked in Question 2. It supplies no correction to the
source's other conjectures and makes no exhaustive priority claim.

## Route

Write a sorted nonnegative quadruple as its list after deleting zero entries.
Its conjugate consists of $d$ copies of $4$, $c-d$ copies of $3$, $b-c$
copies of $2$ and $a-b$ copies of $1$. Deleting a conjugate row therefore
subtracts one from exactly the first one, two, three or four entries,
with a strict gap at the cut. Together with the four row deletions these
are the eight move types in `moves_p4`; `next_order` preserves sortedness.

The private predicate `P` extends the displayed four-row formula to the
empty position, two positive rows with even largest row, and three positive
rows with $a>1$ odd, $b$ odd and either $c>1$ or $b=1$. No one-row position
is losing. `no_P_follower` excludes transitions between candidates;
`non_P_has_follower` constructs a candidate follower for every other
sorted quadruple. `classification` uses strong induction on cell count,
`CrimGrundyRefutation.move_decreases`, `grundy_eq` and `mex_spec` to identify
`P` with Grundy value zero. `result` specializes this to four positive rows.
These private declarations have the same module namespace as `result`.

## Falsifier

A sorted positive quadruple contradicting either direction of the displayed
equivalence would contradict `result`. A mismatch between source row/column
deletion and the imported evaluator would invalidate the source interpretation;
the independent experiment compares the complete move sets in its stated
finite scope. The Lean proof establishes the unbounded statement for the
imported evaluator.

## Evidence

The settling declaration is
`D5.S3.Combinatorics.Games.CrimFourPartClassification.result` in
`D5/S3/Combinatorics/Games/CrimFourPartClassification.lean`.
The Scribe expands the entire proposition and attaches its resolution claim
to this declaration. The source note is `Library/Certificates/basic2026crim.md`.

The independent experiment is [the immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ca04d91f637804d02b14f456fb38a429a6cef487/docs/reports/crim-question-one-four-parts).
Program: `check.py`; SHA-256:
`9105333baa35affba5539f78877a96d6b7714b7dabc5ef43ad0ba7b188875a0f`.
The program read from that commit was executed with
`python3 /Users/auric/.sshx/d3c3bc959a4cb4422eb3599f/attempt-1/experiment-check.py`,
exit 0. It uses exact Python integers and an independent source-move mex
recursion. It checks all 46,376 partitions of width at most 30 and at most
four positive parts, including 40,920 four-part inputs and all thirteen
strategy branches. All checks pass. It also checks Proposition 10 on 465
two-part inputs. This is finite computational evidence, not the unbounded proof.

The four-slot escape audit is unfinished for `result` and the published
owner declarations `sum_nonzero`, `move_decreases` and `grundy_eq`:
[issue #25535](https://github.com/the-omega-institute/trureturing/issues/25535).
No validated registration is asserted. The missing evidence is a lawful
typed realization/readout and its target-specific reconstruction and
sensitivity bridges; infinite-domain templates exist but those bridges
have not been compiled for these targets.

## Triage

| Item | Status and evidence kind |
| --- | --- |
| Exact four-clause classification for every $a\ge b\ge c\ge d\ge1$ without a bound | Proved, kernel-checked `result` |
| Unified classification of sorted nonnegative padded quadruples, hence at most four rows | Proved, kernel-checked private `classification` |
| Every non-P position has a legal P follower, including the thirteen four-row branches; P has no P follower | Proved, kernel-checked private `non_P_has_follower` and `no_P_follower` |
| Source row and conjugate-row-conjugate deletion equal the eight compressed move types; guards preserve sortedness | Proved, kernel-checked private `moves_p4` and `next_order` |
| Independent agreement on 46,376 positions, width at most 30, at most four rows, all thirteen branches; $G([4,3,3,2])=4$, $G([6,4,3,2])=0$, $G([1,1,1])=1$ | Computed, the experiment entry above, exit 0; these exact positive values are not separate Lean claims |
| Complete classification for arbitrary partitions with five or more rows | Open; outside the statement of `result` |
| General positive Sprague–Grundy values for few-row partitions, Question 2 | Open; the classification distinguishes only zero from nonzero |

### What the settlement shows

The decisive mechanism is the two transition properties of `P`, joined to
well-founded cell-count descent and the mex rule. This is proved in the
module by `classification` and `result`. The proof already extends to
all sorted nonnegative padded quadruples and therefore all positions with
at most four rows. The three-row boundary excludes $[1,1,1]$; the independent
experiment computes its value as $1$. This is an exact value from computation,
while the classification proves it is nonzero.

For a winning four-row position, the thirteen branches choose among deleting
the first, second or fourth row, or a column of height one through four.
The parameter splits in `non_P_has_follower` are exhaustive and unbounded.
The finite branch checks are supplementary computational evidence only.
No claim of sharpness beyond the four-row domain is made. The argument
supplies no classification with five rows and no formula for positive values.

The source's printed Conjectures 2 and 3 concern rectairs, with separate
existing refutations. This settlement changes neither of those results.
No dependence of another source theorem on a conjectured answer to Question 1
is identified in the literature screen of #23809.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration records
a bounded source/version, citation, author, arXiv, MathOverflow, Zenodo,
public Lean-settlement, MathDB, thesis and repository screen. No complete
prior answer was found in that searched scope. The 2022 contribution's
locator remains unresolved; rate-limited API queries, bounded broad search
pages and dated local indexes limit coverage. No exhaustive novelty or
priority claim follows from those negative searches. The formal statement
and its kernel proof do not depend on literature completeness.
