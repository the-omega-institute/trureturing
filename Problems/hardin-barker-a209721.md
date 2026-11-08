---
slug: hardin-barker-a209721
bibkey: hardinbarker2012a209721
doi: null
url: https://oeis.org/A209721/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.result
---

# Hardin–Barker three-column clockwise-edge-difference formulas

## Problem

R. H. Hardin's OEIS A209721, revision 43, NAME states:

> 1/4 the number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences.

The FORMULA field states:

> Empirical: a(n) = a(n-1) +2*a(n-2) -2*a(n-3).

> Empirical g.f.: x*(3+x-5*x^2)/((1-x)*(1-2*x^2)). [_Colin Barker_, Mar 23 2012]

The source offset is $1,1$. For a square with top row $a,b$ and bottom row $c,d$, the clockwise differences are the signed integers $b-a,d-b,c-d,a-c$. Every consecutive square is tested. Arrays have labelled rows and columns and entries in $\{0,1,2\}$; no symmetry quotient is taken. The count $a(n)$ is the raw cardinality divided by rational four.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every consecutive square has distinct clockwise edge differences | `IsSourceArray` | The literal four-term integer list is pairwise unequal for every `Fin n` row gap and `Fin 2` column gap. |
| One quarter of the labelled-array count | `a` | `Nat.card` of the full array subtype, coerced to rationals and divided by four. |
| Recurrence at every index at least four | First conjunct of `claim` | $a(m+4)=a(m+3)+2a(m+2)-2a(m+1)$ for every natural $m$. |
| Ordinary generating function | `IsSourceSeries` and the last two conjuncts of `claim` | A rational formal series exists, its constant coefficient is zero, and every such series satisfies the full cross-multiplied identity. |

The source-array predicate inlines the signed-difference list. The proof uses the existing `HardinBarkerA209723EdgeDifferences.DistinctClockwise` definition inside `arrayWalkEquiv`; it introduces no duplicate square predicate. The natural substitution $n=m+4$ exactly covers $n\ge4$. The total auxiliary value $a(0)$ is outside the source domain. Series existence prevents a vacuous universal statement. Since $(1-X)(1-2X^2)$ has constant coefficient one, it is a unit in $\mathbb Q\llbracket X\rrbracket$; cross-multiplication preserves the rational generating-function assertion.

## Motivation

`D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences.result` proves the complete recurrence, existence and generating-identity claim for the literal source arrays. This Tier 1 external named problem is preregistered in [#23890](https://github.com/the-omega-institute/trureturing/issues/23890). Its admission basis is `open-problem-resolution (#23890; Proved)`.

## Gap

The bounded literature screen in #23890 found no inspected source-array proof of the two empirical FORMULA assertions. Programs computing a conjectural sequence do not establish that the English array count has that sequence. The issue also identifies Haobo Ma and Wenlin Zhang's later Zenodo record [23903301](https://zenodo.org/records/23903301), *OEIS A209723: Barker's conjectures on distinct clockwise edge differences*, as mentioning A209721. Its creation is later than the preregistration. This attribution is issue-reported; the live Zenodo API reading returned HTTP 403, so the record's full scope is unverified here. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

`compatibility` proves that the two literal overlapping-square conditions are equivalent to the explicit row relation `Edge`. `arrayWalkEquiv` gives an entry-preserving equivalence between the source arrays and compatible row histories. Its row map is assembled from the existing finite-function equivalences.

For an arbitrary finite type $V$, directed relation $R$, and transfer vector $u$ satisfying $u(0,i)=1$ and $u(n+1,i)=\sum_j [R(i,j)]u(n,j)$, `count_histories` proves that the number of length-$n$ histories is $\sum_i u(n,i)$. The proof partitions histories by first state and second state, uses prepend/tail bijections for the successor fibers, and inducts over unrestricted natural length. It requires neither connectivity nor an edge at every state.

The specialized `u_recurrence` proves $u(n+4,r)+2u(n+1,r)=u(n+3,r)+2u(n+2,r)$ at every state and length. `source_count` transports the generic count through the array equivalence. Summation and rational division by four give `a_recurrence`; `a_initial` gives $a(1)=3$, $a(2)=4$, $a(3)=5$. `series_formula` proves the generating identity by coefficient extensionality. `result` constructs the source series with `PowerSeries.mk` and combines all three assertions. These helpers belong to this module and are not separate frozen prerequisites.

## Falsifier

A literal source count violating the recurrence at an index at least four, or a source series violating the formal identity, would contradict `claim`. A recurrence-defined surrogate, a symmetry quotient, unsigned differences, or finite-prefix agreement would not settle this claim.

## Evidence

The mathematical evidence is the settling `result` and its frozen module state. The public declarations' axiom closures are contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The independent experiment is pinned at [trureturing-experiments, `fc319fd926e2340f6c568cf498fb820357e4be36`, `docs/reports/hardin-barker-a209721/`](https://github.com/the-omega-institute/trureturing-experiments/tree/fc319fd926e2340f6c568cf498fb820357e4be36/docs/reports/hardin-barker-a209721). The command `cd /tmp/op-hardin209721/stage-b-experiment/docs/reports/hardin-barker-a209721 && python3 check.py` runs the archived files from that immutable revision and exits 0 with `ALL_CHECKS_OK`. The SHA-256 of `check.py` is `33f37f5145a55bed5c8bde97c74917e2a6f640b2e6ce35ff88eefe2998eaf704`. It matches all 210 b-file values, direct enumerations at $n=1,2,3$, the parity formulas through $n=210$, Peterson's two-step recurrence for $3\le n\le210$, the homogeneous recurrence for $4\le n\le210$, and exact generating-function convolution through coefficient 210. These are finite computed results.

The four-slot escape audit of the public `result` is unfinished: [#25560](https://github.com/the-omega-institute/trureturing/issues/25560). A faithful reconstruction and sensitivity bridge for the combined recurrence, existence and universal-series statement has not been supplied. No `declared_validated` registration is claimed.

## Triage

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Exact source recurrence, source-series existence and universal generating identity | Proved; kernel-checked | `result`, through `a_recurrence` and `series_formula`, covers every recurrence index $n\ge4$ and every source series. |
| Literal square classification, row table and entry-preserving array/walk equivalence | Proved in prose for the eight-square classification below; kernel-checked for the row table and equivalence | `compatibility` and `arrayWalkEquiv` are used by `source_count`, which is used by `result`. No separate eight-square Lean theorem is asserted. |
| General finite-relation history count, including disconnected graphs and isolated states | Proved; kernel-checked | `count_histories` has arbitrary finite $V$, arbitrary decidable $R$, and arbitrary transfer vector satisfying the displayed zero and successor laws. |
| Independent finite checker | Computed | The immutable experiment and command in Evidence exit 0, with the stated SHA-256 and exact tested ranges. |
| Separate all-index parity and Peterson two-step Lean results | Open as separate formalization obligations | Their finite checks do not constitute new all-index Lean theorems. |
| Widths other than three columns and analytic convergence | Open within this delivery's scope | Neither is a conclusion of this module. |

### What the settlement shows

The decisive mechanism is the literal row-history equivalence together with an all-length transfer-count induction. The generic history theorem extends without change to disconnected finite directed relations and isolated states, provided the same transfer and length-zero laws hold. This extension is kernel-checked by `count_histories`; it assumes no source-specific graph decomposition.

The eight-square classification has the following prose proof. Four distinct differences are chosen from $\{-2,-1,0,1,2\}$ and sum to zero. Since all five numbers sum to zero, the omitted difference is zero. The $+2$ and $-2$ edges cannot be opposite: their forced endpoints make the remaining two differences zero. They are adjacent, giving three consecutive entries $0,2,0$ or $2,0,2$; the fourth entry is $1$. The two patterns and their four rotations are exactly the eight possible squares, and substitution proves the converse. This is proved in prose, not a separate kernel-checked declaration.

The exact row table consists of the two three-vertex paths $010-202-121$ and $101-020-212$, the two edges $021-102$ and $120-201$, and 17 isolated rows. This graph description is mathematical explanation of the explicit table proved by `compatibility`. Branching every two steps explains the factor two; the deterministic components explain the additive term in the neighbouring affine recurrence. The parity formulas and Peterson recurrence are computed only over the finite ranges in Evidence and remain separate all-index formalization obligations here.

The two empirical FORMULA assertions can therefore be used as proved statements about the source-defined three-column arrays. The parent table's other widths and claims depending on them do not follow from this settling theorem. No convergence radius or analytic identity is asserted.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the preregistration's bounded screen includes unavailable indexes, and the later Zenodo record's full scope was not independently read because its API returned HTTP 403. The unfinished four-slot audit is disclosed in #25560. Neither boundary weakens the stated Lean proposition or supplies missing registration evidence.
