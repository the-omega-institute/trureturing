---
slug: fokkink-rust-2024-splythoff-grundy-rows
bibkey: fokkinkrust2024splythoff
doi: 10.1007/s00182-022-00824-1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/SplythoffGrundyRows.result
url: https://arxiv.org/abs/1904.08339
---

## Problem

Robbert Fokkink and Dan Rust, *Queen reflections: a modification of Wythoff
Nim*, arXiv:1904.08339v2, Section 9, printed page 16; International Journal
of Game Theory 53 (2024), 1099–1117, DOI 10.1007/s00182-022-00824-1:

> For Splythoff Nim, it appears that every row or column contains each Sprague-Grundy value once and no more. We do not have a proof for that.

Preregistration: [#15902](https://github.com/the-omega-institute/trureturing/issues/15902).
The statement is proved by `D5/S0/Certificates/Games/SplythoffGrundyRows.result`.
Its bound theorem `row_exists_bound` supplies an occurrence at
$y\le 5x+2g+3$ for every row $x$ and value $g$.

### Statement echo

| Source clause or convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| Two piles, including an empty pile | Natural coordinates in `splythoffMove` and `grundy` | No positivity restriction on positions |
| Reduce one pile | First two disjuncts of `splythoffMove` | The other coordinate is unchanged |
| Remove an equal positive number from both piles | Third disjunct of `splythoffMove` | The same $k$ satisfies $1\le k\le\min(x,y)$ |
| Split only after removing counters from both piles | Fourth disjunct of `splythoffMove` | The smaller pile is positive and the target sum equals $\max(x,y)-\min(x,y)$ |
| Mex of all legal follower values | `followers`, `grundy`, private `followers_iff` and `grundyPair_eq` | Complete legal-follower set and its exact mex equation |
| Every value in each row once and no more | First conjunct of `claim`; `result` | Universal natural row and value, unique natural column |
| Every value in each column once and no more | Second conjunct of `claim`; `result` | Universal natural column and value, unique natural row |
| The preregistered finite bound | `row_exists_bound` | Additional quantitative conclusion, with no extra hypothesis |

The bounded-follower convention repair leaves the literal move relation
unchanged, including the unbounded existential for double moves. The
finite rectangle with both coordinates at most $\max(x,y)$, filtered by
that relation, is exactly its follower set: `follower_bound` proves the
coordinate bound and `followers_iff` proves the equivalence. Every move
strictly decreases the total pile size, and `grundyPair_eq` supplies the
mex equation used by the proof. No legal move is discarded.

## Motivation

The settling node is `D5/S0/Certificates/Games/SplythoffGrundyRows.result`.
It establishes that each infinite row and each infinite column is a
permutation of the natural Grundy values. The quantitative existence
bound makes the row conclusion finite for each specified pair $(x,g)$.
The frozen `D5.S0.Certificates.Games.CrimGrundyRefutation.mex` and
`mex_spec` are reused; their partition-game results are not premises.

## Gap

The source's question about reflected diagonals remains open. Its separate
results on losing positions and Tribonacci representations are not
premises of the row/column proof. The inaccessible Ortega thesis leaves
a literature boundary; no exhaustive prior-art exclusion or claim of
original priority is made.

The escape audit is unfinished for both public theorems `row_exists_bound`
and `result`: [#16101](https://github.com/the-omega-institute/trureturing/issues/16101).
Both candidate registrations decode as `declared_unresolved`, with
`IE-C050 / source.selection_missing`; neither is `declared_validated`.
Missing lawful source-selection evidence remains an audit obligation.

## Route

Swapping piles preserves the move relation. Well-founded induction on
$x+y$ gives `grundy_symm`. A single move connects any two distinct positions
in one row, so `move_value_ne` gives `row_injective`; symmetry gives
`column_injective`. Double moves similarly give `diagonal_injective`.

For a fixed value $g$, `matching` collects ordered representatives
$(u,v)$ with $u\le v$, $u+v\le M$ and $G(u,v)=g$. Equal-valued unordered
pairs share no coordinate unless they coincide. Their two coordinate
images can intersect at at most one diagonal value. The union lies in
$\{0,\ldots,M\}$, hence `matching_card_bound` proves
$2|\mathrm{matching}(g,M)|\le M+2$. The image under summation yields
`targetSums_card_bound`, bounding distinct target sums by
$\lfloor(M+2)/2\rfloor$.

In the window $x<y\le x+M$, the columns with value below $g$ number at most
$g$. Vertical and double value-$g$ followers obstruct at most $x$ columns
each, the $2x$ ordinary-obstruction bound in Landman's Wythoff argument.
The split obstruction is bounded by the target-sum count. If $g$ is absent
up to $x+M$, the mex property makes these sets cover the entire window.
For $M=2g+4x+3$, their combined bound is
$g+2x+\lfloor(M+2)/2\rfloor=M-1$, contradicting the window's size $M$.
This proves `row_exists_bound`; row injectivity and symmetry give `result`.

## Falsifier

A position violating the exact single, double or split correspondence, a
failure of mex exclusion, or a row/value pair lacking the stated unique
occurrence would contradict the specified claim. The kernel-checked
`result` rules out such a pair within these definitions and the standard
axiom closure. A proof of prior settlement in the inaccessible thesis
would change the literature assessment, not the Lean theorem.

## Evidence

The mathematical evidence is the compiled settling module and its six
public Scribe nodes. The axiom closure of every public declaration is
contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The positive result and its bound are both escape-audit targets; the
linked unfinished audit is independent of this mathematical closure.

### Finite experiment

[Experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/c055a20a28ca440627b14c3784a555fc134f5d3f/docs/reports/fokkink-rust-2024-splythoff-grundy-rows)
at commit `c055a20a28ca440627b14c3784a555fc134f5d3f`.
Command in that entry: `python3 check.py`; exit 0; final reading `bad=0`.
SHA-256 of `check.py`:
`c27eb6a0724c8fec1dbe113ae5ece31d75e357daff8ca4e1430c3b05e3d52298`.
SHA-256 of its compiled input `sg.c`:
`30aeba72085250fa1697a2fc2107fba916cf81b570593e251ea72c0b900cbaff`.

Computed scope: $[0,900]^2$; rows $x\le100$ and values $g\le150$ give
15,251 checked pairs, each with exactly one occurrence in the tested row
and with $y\le5x+2g+3$. Symmetry and row injectivity are checked on the
finite square. Rows 0, 1, 15 and 16, columns 0 through 17, agree with the
source's Table 6. These are finite computations; the unrestricted
row/column statement is supplied by `result`.

## Triage

### What the settlement shows

- **Mechanism — kernel-checked.** `matching_coordinate_disjoint`,
  `matching_card_bound` and `targetSums_card_bound` prove the sparse-sum
  estimate for fixed-value split targets. `obstruction_card` proves the
  $2x$ ordinary-obstruction bound. `window_cover` and `row_exists_bound`
  force an occurrence in a window of length $2g+4x+3$; `result` proves
  unique existence in every row and column. There are infinitely many
  split opportunities across a row, but the relevant target sums obey
  the finite matching bound. Sharpness of $5x+2g+3$ is open.
- **Robustness — proved in prose.** Keep all Wythoff moves and choose any
  swap-invariant subset of the reflected split moves. Every retained
  move still decreases the pile sum, and swap invariance gives symmetry
  by the same induction. Keeping all single and double moves preserves
  row, column and diagonal injectivity. Thus equal-valued unordered
  pairs have disjoint coordinates except for the one possible diagonal
  pair, giving the same matching and sum bounds. If a value is absent
  in the counting window, mex supplies a follower of that value; a
  retained split follower still has sum $y-x$, so its obstruction lies
  in the same target-sum set. Removing split moves cannot enlarge that
  obstruction set. The bounds $g$, $2x$ and $\lfloor(M+2)/2\rfloor$
  again give $M\le M-1$. Therefore the row/column property and the bound
  extend to this whole class. This is a prose proof, not an additional
  kernel-checked family theorem.
- **Diagonals — open.** The source's second remark, that reflected
  diagonals contain every value, is not settled here. Plain diagonals
  miss values: the source states that $(n,n+3)$ misses 0 and $(n,n+4)$
  misses 1 (Section 9, printed pages 16–17; literature reading).
- **Readings — computed.** The experiment entry and exact tested scope
  in Evidence give `bad=0`, including the source's four Table 6 rows
  and the 15,251 bounded row/value checks. No infinite conclusion is
  inferred from that computation.
- **Ortega thesis — ASSUMED-UNVERIFIED.** The 2021 Ateneo de Manila MSc
  thesis could not be retrieved (HTTP 403; Firecrawl HTTP 402). Its
  title concerns losing positions; its treatment of this Grundy
  question is unverified.

The settled row/column remark is affirmative. The source's losing-position
and Tribonacci results remain separate, and the reflected-diagonal
question remains open; no other source result is claimed to follow from
this proof. The bound also transfers to columns by pile symmetry.

## ASSUMED-UNVERIFIED

Ortega's 2021 MSc thesis is not cleared by a full-text reading. The cited
accessible literature screen does not establish exhaustive priority.
The uniform robustness conclusion is proved in prose and is not part of
the module's public kernel-checked surface. Optimality of the numerical
bound and the reflected-diagonal question remain open.
