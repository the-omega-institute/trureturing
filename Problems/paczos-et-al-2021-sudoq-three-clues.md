---
slug: paczos-et-al-2021-sudoq-three-clues
bibkey: paczosetal2021sudoq
doi: 10.1103/PhysRevA.104.042423
url: https://arxiv.org/abs/2106.02967v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/LatinSquares/SudoQMinimumClues.result
---

# Four clues are necessary for unique four by four SudoQ solvability

## Problem

J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt and K. Życzkowski,
*Genuinely quantum SudoQ and its cardinality*, arXiv:2106.02967v2,
Section III.A, page 4, state:

> **Conjecture.** Similarly to the classical Sudoku there are no $4\times4$ SudoQ with 3 clues that are uniquely solvable.

G. Rajchel-Mieldzioć, *Quantum mappings and designs*, arXiv:2204.13008,
Chapter 7, restates it:

> Uniquely solvable grids of $4 \times 4$ SudoQ admit at least 4 clues.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| A quantum Latin square has orthonormal rows and columns. | `SudoQClueGeometry.IsSudoQ` | Four vectors in $\mathbb C^4$ in each row and column. |
| Every disjoint block is an orthonormal basis. | `IsSudoQ` and `blockCell` | Four $2\times2$ blocks; zero-based coordinates $(2b_1+k_1,2b_2+k_2)$. |
| A quantum grid has blank entries; its clues are the nonblank entries. | `C` and `v` in `IsSolution` | A finite set of cells with literal prescribed vectors; values outside `C` impose no constraint. |
| Solvability includes existence of a completion. | `UniquelySolvable` | Its existential quantifier supplies an `IsSolution`. |
| Solutions agree up to phase. | `SameRays` | A separate complex scalar of norm one for each entry. Clues remain literal vector equalities. |
| No uniquely solvable grid with three clues. | `SudoQMinimumClues.claim` and `result` | At most three clues, hence also exactly three; arbitrary clue values, including unsolvable grids. |

`RayEq` and `HasRepeatedRay` are auxiliary predicates for a pair of vectors
and for one ray occurring once in every unit. They add no hypothesis to the
settled claim. The four-dimensional specialization is the source's $N=2$
SudoQ, not the $N=4$ Sudoku parameter.

## Motivation

The source's Theorem 13 supplies uniquely solvable four-clue grids. The
kernel-checked `D5/S3/Quantum/LatinSquares/SudoQMinimumClues.result` supplies
the lower bound for all grids, settling the conjecture as **Proved**.
Preregistration #15470 identifies the external question and its conventions.
There is no digestion atom or coverage step.

## Gap

The arXiv v2 source and the thesis state the conjecture. The literature
screen recorded in #15470 covers arXiv SudoQ/quantum-Sudoku results and eight
Semantic Scholar citing works, including quantum Latin-square cardinality
and orthogonal-Sudoku constructions. No earlier settlement was found in
that searched scope. This does not establish exhaustive literature
completeness or priority. The PRA full text and the publisher full text of
DOI 10.1002/qute.70293 remain unverified.

## Route

The supporting theorem `unique_implies_repeated_ray` uses the span $S$ of
the clues. Three clues imply $S\ne\mathbb C^4$. Reflection in $S$ fixes every
clue; uniqueness as rays forces each completion entry into $S$ or $S^\perp$.
The consumed `unique_K_no_pair` constructs a clue-fixing swap to exclude
two distinct orthogonal entries of a row in $S^\perp$. The complement is a
line, and its unit ray occurs once in every row, column and block.

The settling proof brings those four occurrences to a canonical pattern by
Sudoku-preserving permutations. Orthogonality yields one of two normal
forms related by transposition. Four disjoint rectangles partition the
cells, each permitting a swap of two orthogonal rays. At most three clues
miss one rectangle. Its trade gives a second completion differing as a ray;
outside the rectangle the original vectors are literally unchanged.

## Falsifier

A uniquely solvable $4\times4$ SudoQ with at most three clues would contradict
`result` under the definitions above. A different convention for equality
of completions, clue constraints, or block coordinates requires a separate
statement. The numerical experiment alone does not prove the universal
claim. The source's four-clue existence construction is literature evidence,
not a new kernel-checked declaration in this delivery.

## Evidence

The Lean modules are `D5/S3/Quantum/LatinSquares/SudoQClueGeometry.lean` and
`D5/S3/Quantum/LatinSquares/SudoQMinimumClues.lean`. The axiom closure of every
public declaration is contained in $\{\texttt{propext},\texttt{Classical.choice},
\texttt{Quot.sound}\}$. Canonical Freeze events provide statement identities.

Escape audit unfinished: [#15607](https://github.com/the-omega-institute/trureturing/issues/15607).
The inspected pointwise, guarded, iff and existential templates do not
supply the full dependent completion family and existential ray witnesses.
`DependentFamily` lacks the source-bound arena, exact reconstruction and
occurrence selection, equivalence bridge, whole-family variation and
sensitivity, and actual observational dependence needed here. Zero-vector
fibers of the general ray lemmas remain in scope. No Reg file is delivered.
The current DTR reading is DTR-Unregistered for the ten public theorem audit
targets; it is an Observe diagnostic and does not complete registration.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Mechanism: clue-fixing reflection/swap, repeated-ray normalization, and a clue-free rectangle trade produce a second completion with a changed ray. | Proved | Kernel-checked `SudoQClueGeometry.unique_implies_repeated_ray` and `SudoQMinimumClues.result`; all grids with at most three clues and arbitrary complex clue vectors. |
| Symmetry orbit, forced normal-form equalities, rectangle trades and end-to-end numerical checks. | Computed | The pinned experiment entry below; exactly 16 repeated-ray patterns, 300 random instances alternating between the normal form and its transpose (150 each), and 2000 random three-clue solutions. |
| The minimum number of clues for uniquely solvable $4\times4$ SudoQ is exactly four. | Proved in prose | `result` gives the lower bound; the source's Theorem 13 gives a uniquely solvable four-clue example. Thus the minimum is both at least and at most four. |
| The minimum number of clues for uniquely solvable $9\times9$ SudoQ. | Open | Neighbouring question; neither this fixed-dimension Lean proof nor the experiment determines it. |

### Experiment entry

[Published numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/70eb46c96611a26464b7f8ea3330a67ffce8a605/docs/reports/paczos-et-al-2021-sudoq-three-clues).
Command: `python3 check.py` in that directory; exit 0; script SHA-256
`e37ab13c1f3122f7063ceed89cb700c075970ebf88d9bdb23624fdb5476a83d8`;
final reading `bad= 0`. The 16 patterns form one orbit under the tested
Sudoku symmetries, whose generators preserve all 12 units. Closure of the
three-shared-rays rule gives the canonical normal-form equalities. The
random trade and end-to-end checks use the exact finite scope listed above;
The experiment compares clue values as rays; literal clue equality is supplied by the Lean proof. No numerical universal claim follows.

The lower bound includes zero, one and two clues as well as three. The
source's cardinality classification and four-clue construction remain
literature results unaffected by the settlement. No $9\times9$ conclusion,
classification of all four-clue grids, or kernel formalization of Theorem 13
is asserted.

## ASSUMED-UNVERIFIED

Unindexed literature and inaccessible publisher full texts are not excluded.
No exhaustive novelty or model-diversity claim is made. The exact-four
consequence uses the source's Theorem 13 as literature evidence. Four-slot
escape registration remains unfinished under #15607.
