---
slug: hardin-barker-a209723-edge-differences
bibkey: hardinbarker2012a209723
doi: null
url: https://oeis.org/A209723/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.result
---

# Hardin–Barker five-column clockwise-edge-difference formulas

## Problem

R. H. Hardin's OEIS A209723, revision 11, NAME states:

> 1/4 the number of (n+1) X 5 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences.

The FORMULA field states the empirical recurrence and Colin Barker's conjectures:

> Empirical: a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3).

> G.f.: x*(6 + x - 11*x^2) / ((1 - x)*(1 - 2*x^2)).

> a(n) = 3*2^(n/2 - 1) + 4 for n even.

> a(n) = 2^((n + 1)/2) + 4 for n odd.

The offset is $1,1$. Entries are labelled; no symmetry quotient is taken. For a square with top row $a,b$ and bottom row $c,d$, the differences are the signed integers $b-a,d-b,c-d,a-c$. Let $a(n)$ be one quarter of the number of valid $(n+1)$-by-$5$ arrays in the rationals.

### Statement echo

| Source clause | Lean counterpart | Domain and fidelity |
| --- | --- | --- |
| Distinct clockwise differences | `DistinctClockwise` | Four integer differences, pairwise unequal; entries have type `Fin 3`. |
| Every consecutive square | `IsSourceArray` | Every `Fin n` row gap and `Fin 4` column gap is tested. |
| One quarter of the array count | `a` | `Nat.card` of the entire labelled-array subtype, coerced to rationals and divided by four. |
| Positive even formula | First conjunct of `claim` | $a(2(m+1))=3\cdot2^m+4$ for every natural $m$. |
| Positive odd formula | Second conjunct of `claim` | $a(2m+1)=2^{m+1}+4$ for every natural $m$. |
| Recurrence | Third conjunct of `claim` | $a(m+4)=a(m+3)+2a(m+2)-2a(m+1)$ for every natural $m$. |
| Ordinary generating function | `IsSourceSeries`, fourth and fifth conjuncts of `claim` | Existence and the identity for every rational formal series with zero constant coefficient and coefficient $a(n)$ for $n\ge1$. |

The natural-index substitutions exactly cover the source domains. The extra series-existence conjunct prevents a vacuous universal assertion. The generating identity is cross-multiplied by $(1-X)(1-2X^2)$, whose constant coefficient is one. The auxiliary value $a(0)$ is outside the source formulas and does not supply the series constant term.

## Motivation

`D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209723EdgeDifferences.result` proves the full five-conjunct claim. This is a Tier 1 external named open-problem settlement, preregistered in issue [#24091](https://github.com/the-omega-institute/trureturing/issues/24091). The source formulas count the literal arrays at every positive height.

## Gap

The bounded literature screen in #24091 identifies Andrew's Math Stack Exchange answer [4995628](https://math.stackexchange.com/a/4995628) as giving the local eight-square classification and a related four-column count. It does not settle the five-column count. The inspected sequence programs evaluate the conjectural formulas without counting the source arrays. No five-column settlement was found in that screened scope; literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Rows have carrier `Fin 5 → Fin 3`. The private `compatible_neighbors` theorem identifies the literal adjacent-square condition with an explicit finite neighbor table. The private `sourceWalkEquiv` uses explicit inverse row maps, and `source_card` equates the source-array cardinality with the sum of row-chain cardinalities.

The private `walks_parity` is an induction over arbitrary natural $m$. For every starting row $s$ it proves

$$
\operatorname{walks}(2m+1,s)=2^m\operatorname{degreeBranch}(s)+\operatorname{deterministic}(s),
$$

$$
\operatorname{walks}(2m+2,s)=2^{m+1}\operatorname{branch}(s)+\operatorname{deterministic}(s).
$$

Here the branching indicator has six supported starts, the branching degree sums to eight, and the deterministic indicator has sixteen supported starts. The raw odd and even totals are $8\cdot2^m+16$ and $6\cdot2^{m+1}+16$. Rational division by four gives the two formulas. The private `lag_two` gives the affine two-step relation; `recurrence` gives the homogeneous recurrence. `series_exists` constructs the formal series, and `series_identity` proves its identity by coefficients. These are declarations of the settling module, not separately frozen prerequisites.

## Falsifier

A valid positive-height array count differing from either parity formula, a recurrence violation at an index at least four, or a source formal series violating the cross-multiplied identity would contradict `claim`. Kernel verification establishes `result` for the stated definitions and standard axiom boundary. Finite numerical agreement alone is not this all-height conclusion.

## Evidence

The mathematical evidence is the settling module and its frozen `result`. Its public axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The independent computation is [the experiment directory pinned to `bd51c45126c7414a963b297ddf7db69624bbbc21`](https://github.com/the-omega-institute/trureturing-experiments/tree/bd51c45126c7414a963b297ddf7db69624bbbc21/docs/reports/hardin-barker-a209723). The pinned `check.py` has SHA-256 `659ba9afc655bb4e97959ebc51605038171dc2c341ff6ae34b1c21e695f6f801`; the accompanying `b209723.txt` has SHA-256 `67c1ee54560cfb5da53a7bdf7b21b4141856fff5321130ba8d1145d9d341305b`. Both files were read from that immutable commit. Running the materialized script with `python3 /Users/auric/.sshx/f6058555b84ad5dff781b0b9/attempt-1/check.py` exited 0 and returned `ALL_CHECKS_OK`.

That computation checks all 81 local squares and 59,049 ordered row pairs; it finds 24 arcs, 12 undirected edges and graph $2P_3\sqcup8K_2\sqcup221K_1$ on 243 rows. Independent entry-by-entry enumeration for $n=1,\ldots,8$ gives raw counts $24,28,32,40,48,64,80,112$. The graph counts divided by four match all 210 official b-file terms. The script checks parity for $1\le n\le210$, the recurrence for $4\le n\le210$ and the cross-multiplied series coefficients for $0\le n\le210$. These are computed finite statements.

The public theorem's four-slot escape audit is unfinished in [#24684](https://github.com/the-omega-institute/trureturing/issues/24684). No successful registration or `declared_validated` status is asserted.

## Triage

`theorem`; Proved. The admission basis is `open-problem-resolution (#24091; Proved)`; generality is `G`, and utility is `none`.

### What the settlement shows

| Target item | Status | Evidence kind and exact scope |
| --- | --- | --- |
| Affine two-step relation | proved | Kernel-checked private `lag_two`: $a(n+3)=2a(n+1)-4$ for every natural $n$. |
| Literal arrays equal row chains | proved | Kernel-checked private equivalence `sourceWalkEquiv` and theorem `source_card`, for every natural $n$; the inverse maps preserve the literal square condition. |
| Complete neighbor relation | proved | Kernel-checked private `compatible_neighbors`; the defining table is empty outside the 22 listed rows. No separately named isolated-row-cardinality theorem is asserted. |
| Unbounded continuation from every row | proved | Kernel-checked private `walks_parity`: both displayed formulas hold for every natural $m$ and every starting row $s$. |
| Factor two and deterministic constant four; source formulas and recurrence | proved | Kernel-checked private `step_basis`, `sum_deterministic`, `raw_odd`, `raw_even`, `a_odd`, `a_even`, `recurrence`, and public `result`; domains are all positive parity indices and all recurrence indices at least four. |
| Source series exists and every such series satisfies the identity | proved | Kernel-checked private `series_exists`, `series_identity`, and public `result`, in rational formal power series; no analytic-convergence premise. |
| Graph $2P_3\sqcup8K_2\sqcup221K_1$ and agreement with 210 b-file terms | computed | The pinned experiment and exact command, exit 0 and SHA-256 given in Evidence. The edge-table equivalence is separately kernel-checked by `compatible_neighbors`; no named graph-isomorphism theorem is asserted. |
| General widths and analytic interpretations | open | Outside the five-column formal claim; no uniform-width theorem or analytic convergence theorem is asserted. |

The decisive mechanism is the two-step branching law for arbitrary walk length, combined with the literal array/chain equivalence. The statement extends over every source height, rather than only a tested range. It requires exactly five columns and ternary entries. The neighboring four-column result and other widths remain separate claims; no result depending on a broader conjecture is certified here. Formal power-series equality does not establish an analytic interpretation.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority remain `ASSUMED-UNVERIFIED`. The bounded source screen in #24091 includes OEIS, the related four-column discussion, sequence programs, public formalization catalogues, arXiv metadata and a synthesis paper's source, Crossref and Zenodo. Exhaustive citing-paper coverage, complete author bibliographies and unrestricted public-repository body searches were not established. No source DOI or source-paper arXiv identifier was identified. The unfinished escape audit is tracked by #24684 and is independent of the proved mathematical claim.
