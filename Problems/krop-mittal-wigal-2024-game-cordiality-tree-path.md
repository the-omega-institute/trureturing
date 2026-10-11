---
slug: krop-mittal-wigal-2024-game-cordiality-tree-path
bibkey: kropmittalwigal2024cordiality
doi: 10.1007/s00373-024-02798-1
url: https://arxiv.org/abs/2403.18060v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Games/CordialityTreePathRefutation.result
---

# The tree–path conjecture for the game cordiality number

## Problem

Krop, Mittal and Wigal, *The Cordiality Game and the Game Cordiality Number*,
arXiv:2403.18060v1 (2024), published as *Graphs and Combinatorics* 40 (2024),
article 75, state in Section 3, Conjecture 3.2:

> For any tree $T$ of order $n$, $c_g(T)\le c_g(P_n)$.

Their Section 1 defines the cordiality game: Admirable labels a selected
vertex by $0$, Impish labels one by $1$, edge labels are sums modulo $2$,
and the discrepancy is $d=|e_1-e_0|$. Admirable starts in $c_g$ and minimizes
the terminal discrepancy while Impish maximizes it.

## Motivation

The settling module gives a ten-vertex tree whose game cordiality number is at
least three, while an explicit Admirable strategy holds the path value at most
one. Since the path has nine edges, its value is exactly one, so the universal
tree–path comparison is false.

## Gap

The preregistered question is issue [#15128](https://github.com/the-omega-institute/trureturing/issues/15128),
which records the source definitions, the tree, the pairing route, the path
strategy, the minimax convention, and the literature screen before the Lean
formalization. The module repairs the source quantification by making both
adjacency relations explicit `DecidableRel` binders; this is an elaboration
repair preserving the source's quantifiers.

## Route

The module defines the finite game state, edge counts, discrepancy, backward
induction value and $c_g$. It proves the minimax correspondence by strong
induction. For the path on ten vertices, the finite strategy table and its
soundness theorem give $c_g(P_{10})\le1$. For the tree with path edges
$\{\{i,i+1\}:0\le i\le6\}$ and pendant edges $\{\{0,8\},\{0,9\}\}$,
Impish pairs $(0,4),(1,5),(2,6),(3,7),(8,9)$ and responds with the partner.
The kernel-checked finite terminal bound `terminal_bound` proves
$3\le d$ for every terminal transversal of this pairing. The strategy and
minimax correspondence give $3\le c_g(T)$ (`witness_lower`), while explicit
walks and the nine-edge count prove that the witness is a tree. The signed-edge
identity explains the strategy; it is a paper argument below, not a Lean theorem.

## Falsifier

The refutation would fail if the witness were not a tree, if the pairing move
were illegal, if a terminal pairing transversal had discrepancy below
three, if the path strategy did not establish the bound one, or if the
minimax transfer were unsound. These finite and strategy conditions are checked in Lean, culminating
in `result : ¬ claim`.

## Evidence

`D5/S3/Combinatorics/Games/CordialityTreePathRefutation.result` is the settling
declaration and the Scribe records one `OpenProblemResolutionClaim` with
resolution `Refuted` for this dossier. The public definitions are `free`,
`e1`, `e0`, `discrepancy`, `gameValue`, `cg`, and `claim`; the remaining
supporting declarations are private and consumed by `result`.

The numerical reading is the experiment entry
[`docs/reports/krop-mittal-wigal-2024-game-cordiality-tree-path/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/f0c0fb2f703f28e383c5a81d6bd31ee0adcccae5/docs/reports/krop-mittal-wigal-2024-game-cordiality-tree-path)
in `the-omega-institute/trureturing-experiments` at commit
`f0c0fb2f703f28e383c5a81d6bd31ee0adcccae5`. Running `python3 check.py` exits
0 and reports `cg(P10)= 1 cg(T)= 3`, pairing lower bound $3$, the $r=1$
and $r=2$ family readings below, and `bad= 0`. The script SHA-256 is
`747dddafc996bc5bfa2dab32c503e0ac78bea95ad7cd5d4839432a5076cc663d`.

## Triage

The conjecture is refuted under `admission_basis: open-problem-resolution`
(`#15128; Refuted`). The public result is the designated refutation result
(`basis=refutes`) and is exempt from four-slot escape registration
(CLAUDE.md §3.9).

### What the settlement shows

- **The mechanism (proved; kernel-checked bounds).** Impish uses
  $(0,4),(1,5),(2,6),(3,7),(8,9)$. `pairedDisjoint_step` preserves legal,
  disjoint paired states. `terminal_bound` checks the finite terminal
  discrepancy bound $3\le d$ under this pairing; it does not state a
  signed-edge identity. `pairingValue_ge_three`, `pairingValue_le_gameValue`
  and `witness_lower` prove $3\le c_g(T)$. `aCheckFast_sound` and
  `path_upper` prove $c_g(P_{10})\le1$.

- **The sign explanation (proved; paper argument).** With
  $s_v=(-1)^{\mathrm{label}(v)}$, opposite labels give $s_{v'}=-s_v$ on
  each pair. The pendant edges cancel because
  $s_0(s_8+s_9)=0$. Put $a=s_0s_1$, $b=s_1s_2$, $c=s_2s_3$.
  The seven path edges sum to $2(a+b+c)-abc$. For $a,b,c\in\{-1,1\}$,
  this is $5,-5,3,-3$ according as there are three, zero, two or one
  positive signs. Hence $d\ge3$. This identity is explanatory mathematics,
  not a theorem in the Lean module.

- **The path equality (proved; kernel-checked upper bound and paper parity
  argument).** The path has nine edges, so $e_1-e_0=2e_1-9$ is odd and
  $d\ge1$. Together with `path_upper`, this gives $c_g(P_{10})=1$.
  **The witness equality (computed).** The pinned experiment computes
  $c_g(T)=3$; Lean proves only $3\le c_g(T)$.

- **The family (computed for exactly $r=1,2$).** Attaching $2r$ leaves to
  vertex $0$ of $P_8$ gives trees $T_r$ of order $8+2r$. The experiment
  computes $c_g(T_r)=3>1=c_g(P_{8+2r})$ for $r=1,2$ (orders $10,12$).
  **The uniform lower bound (proved; paper argument).** Pair the $2r$
  leaves among themselves and retain $(0,4),(1,5),(2,6),(3,7)$.
  Each leaf pair cancels at vertex $0$, leaving the same signed-edge
  identity and giving $3\le c_g(T_r)$ for every $r\ge1$.
  This family argument is not formalized in the delivered module.

- **Readings (computed).** The single pinned experiment entry in Evidence,
  run as `python3 check.py`, exits 0 with the script SHA-256 stated there.
  Its exact tested scope is $c_g(P_{10})=1$, $c_g(T)=3$, pairing lower
  bound $3$ on $T$, and $r=1,2$ with both tree and path values $3,1$;
  `bad= 0`.

- **Open.** Whether $c_g(P_n)=1$ for all even $n\ge10$ (and hence this
  family refutes the conjecture at every even order at least ten), the
  largest $c_g$ over trees of order $n$, and the Impish-starts variant.

The refutation removes the universal tree–path conjecture as a premise. Any
later result using it must either restrict its tree family or supply a new
hypothesis; the source's separate definitions and unrelated bounds are not
settled here.

## ASSUMED-UNVERIFIED

The literature status is the bounded source and citation screen recorded in
issue #15128 and the Library note; it is not an exhaustive claim about every
later publication. The exact tree and path values beyond the computed orders and the
Impish-starts question are open; the uniform family lower bound has only
the paper argument above.
