---
slug: lee-liu-2025-integer-two-domination-three-row
bibkey: leeliu2025integerdomination
doi: 10.48550/arXiv.2502.00134
url: https://arxiv.org/abs/2502.00134
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.result
---

# Lee–Liu integer {2}-domination of three-row grids

## Problem

Jia-Ying Lee and Chia-An Liu, *The integer {2}-domination number of grids*,
arXiv:2502.00134v1, Conjecture 2.5:

> For positive integer n, we have γ{2}(G3,n) = ⌊3n/2⌋ + 1.

The settlement is **Proved** for every positive width. Its preregistration is
[#17651](https://github.com/the-omega-institute/trureturing/issues/17651).
Here $G_{m,n}=P_m\mathbin{\square}P_n$. An integer {2}-dominating function assigns
each vertex a value in $\{0,1,2\}$ and has sum at least $2$ on each closed
neighbourhood; $\gamma_{\{2\}}$ is the minimum total weight.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Cartesian product of paths $P_m\mathbin{\square}P_n$ | `grid m n`, using `SimpleGraph.pathGraph` and `SimpleGraph.boxProd` | Vertices in `Fin m × Fin n` represent the source's one-based labels. |
| Values in $\{0,1,2\}$ | `IsTwoDominating m n f` bounds every natural value by $2$ | Exactly the abstract and Section 4 domain. |
| Sum on each closed neighbourhood is at least $2$ | The second conjunct of `IsTwoDominating` adds the vertex value to its open-neighbour sum | Each closed-neighbourhood vertex is counted once. |
| Minimum total weight | `gamma2 m n` is the natural infimum of attained feasible weights | The constant function $2$ is feasible, so the weight set is nonempty and its infimum is its minimum. |
| Every positive integer $n$ | `claim` quantifies over every natural $n$ with $1\le n$ | No upper cutoff or additional hypothesis. |
| $\lfloor3n/2\rfloor+1$ | Natural division in `claim` | Natural division equals the floor for these nonnegative integers. |
| Equality for three rows | `result : claim` | Both bounds, including width $1$, are proved. |

Section 1 also allows arbitrary nonnegative integer values. Truncating each
value at $2$ preserves feasibility: a neighbourhood containing a value at least
$2$ still has sum at least $2$, and otherwise its values are unchanged. Weight
cannot increase. Thus the two minimum-weight formulations coincide. This
correspondence is a prose argument; the Lean predicate uses the bounded domain.
The general row parameter in the definitions names the graph family and adds no
hypothesis to the three-row conclusion.

## Motivation

Theorem 2.4 supplies the alternating-column upper bound. Remark 2.6 reports that
the authors' algorithm returns this value for every input width, while explicitly
declining to assert the universal equality. The declaration
`D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.result`
proves that universal equality.

## Gap

The missing lower bound is uniform in the width. Finite transfer computations
alone establish only their tested widths. The potential certificate below
converts local column constraints into a bound for every length.

## Route

Write the zero-padded columns as $x_0=0,x_1,\ldots,x_n,x_{n+1}=0$.
Each column is one of $27$ ternary triples. If $s$ denotes column weight and
$A(a,b,c)$ the three closed-neighbourhood inequalities at the middle column,
feasibility is exactly $A(x_{j-1},x_j,x_{j+1})$ at every actual column.
Equivalently this is a walk with column labels; the transfer states are pairs
of columns, with up to $27^2$ states.

An integer table $R$ defines $\Phi(a,b)=2s(a)+2s(b)+R(a,b)$ and satisfies

$$\Phi(0,b)\le 2s(b)-3,$$
$$A(a,b,c)\Longrightarrow\Phi(b,c)\le\Phi(a,b)+2s(c)-3,$$
$$A(a,b,0)\Longrightarrow1\le\Phi(a,b).$$

The initial and step inequalities telescope to $1\le2W-3n$.
Since $W$ is an integer, $W\ge\lfloor3n/2\rfloor+1$.
For the upper bound, even-numbered columns are $(1,1,1)$; column $1$ and the
last column when $n$ is odd are $(0,1,0)$; other columns are zero. Width $1$
uses $(0,2,0)$. This is feasible and has the required weight. The minimum-weight
assembly uses `Nat.sInf_le` and `le_csInf`.

## Falsifier

A falsifier would be a positive width with a feasible function of smaller
weight, or a failure of the proposed upper construction. The theorem `result`
rules out both for the declared grid and domination predicate. An incorrect
table entry would instead invalidate one of the kernel-checked finite
inequalities; all three finite obligations are proved in the module.

## Evidence

- **Kernel-checked:** `result` proves the exact value for all $n\ge1$.
  The public theorem `column_reduction` and private lemmas `L1`, `L2`, `L3`, `potential_prefix`,
  `sequence_lower_bound`, `lower_bound`, `upper_dominating` and `upper_weight`
  supply the correspondence, potential inequalities, lower bound and upper bound.
  The certificate slices use kernel `decide`, with no `native_decide`.
- **Computed:** [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/e80abbfc67f794121eddc2c3517290b23383c2b9/docs/reports/lee-liu-2025-integer-two-domination-3xn).
  Command: `python3 -I check.py`, executed with the script and certificate from
  that directory; exit $0$, `ALL_OK`.
  `check.py` SHA-256: `28e265bf9eca464ac855827536720068fced40b80c666314b5adf60d80339d47`.
  `certificate.json` SHA-256: `fb14d1db574895826a0a3609491c858849b033d41728d30e383d536c5d9d8bf4`.
  The checks cover all $17{,}138$ admissible triples and $533$ terminal pairs,
  exact transfer minima for $1\le n\le40$, and the construction for
  $1\le n\le40$. These finite readings do not by themselves assert an unbounded result.
- **Escape audit unfinished:** [#17855](https://github.com/the-omega-institute/trureturing/issues/17855)
  covers the public theorems `result` and `column_reduction`. No four-slot registration is supplied;
  the dependent-family source reconstruction, realization bridge, variation,
  sensitivity and observational-dependence evidence remain missing. No
  `declared_validated` status is claimed.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and scope |
| --- | --- | --- |
| Local column mechanism | Proved, kernel-checked: `column_reduction` and `three_column_reduction` | A column constraint depends on its preceding, current and following columns. There are $27$ possible three-row columns; transitions are between column pairs. |
| Potential mechanism | Proved, kernel-checked: `L1`, the $27$ slices of `L2`, the $27$ slices of `L3`, and their aggregate lemmas | The displayed initial, step and terminal inequalities hold for all encoded columns. |
| Telescoping lower bound | Proved, kernel-checked: `potential_prefix`, `sequence_lower_bound` and `lower_bound` | Every feasible function has $2W\ge3n+1$, hence $W\ge\lfloor3n/2\rfloor+1$. |
| Exact strength and sharpness | Proved, kernel-checked: `upper_dominating`, `upper_weight` and `result` | Equality holds for every $n\ge1$; the source's alternating construction attains the lower bound. |
| Remark 2.6 | Proved, kernel-checked: `result` | Its algorithmic equality is a theorem for every positive width. Theorem 2.4's upper bound is sharp. |
| Four-row consequence | Proved in prose as an interface statement | The public definitions `grid`, `IsTwoDominating` and `gamma2` already accept any row count and can be used for Conjecture 3.7 in #17664. The public `column_reduction` theorem, with `pad` and `ColumnA`, supplies the neighbourhood equivalence for every row count. This settlement proves no four-row formula; the $27$-column certificate is specific to three rows. |
| Larger row counts | Open | Exact formulas for $m\ge5$ are not established here. |
| Higher domination threshold | Open | Integer $\{k\}$-domination of grids for $k\ge3$, as proposed in the source's future-work discussion, is not established here. |
| Finite experiment | Computed: the pinned experiment in Evidence, exit $0$, with the listed SHA-256 values | The certificate is checked exhaustively; exact minima and the construction are checked only for $1\le n\le40$. |
| Literature | Literature reading; completeness `ASSUMED-UNVERIFIED` | The source is read. OpenAlex records zero citing works. The related circulant work arXiv:1905.03388 concerns a different graph family. NYCU and other grid-domination theses have not been read in full. |

The decisive feature is a bounded-memory potential whose local inequalities
are independent of the total width. Its finite domain controls an arbitrarily
long sum, while the construction proves sharpness. A corresponding certificate
for another row count or threshold is an open extension of this argument,
not a consequence of this certificate. No additional theorem in the source is
asserted to follow beyond the three-row equality and sharpness stated above.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the preregistration records the
source and repository screens, arXiv and web searches, and the unread thesis
boundary. OpenAlex's source record reports zero citing works at the queried
API endpoint; citation absence is not a proof that no independent settlement
exists. The related circulant literature does not settle this grid statement.
The full NYCU and other theses remain unread. Four-slot escape registration
remains unfinished under #17855; this does not qualify the kernel proof.
