---
slug: ayyer-misra-2023-half-density-most-likely-occupation
bibkey: ayyermisra2024kexclusion
doi: 10.1088/1751-8121/ad5edd
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.result
url: https://arxiv.org/abs/2310.03343v2
---

# Half-density modes of the asymmetric K-exclusion process

## Problem

A. Ayyer and S. Misra, *An exactly solvable asymmetric K-exclusion
process*, arXiv:2310.03343v2, Section 4.5, page 21:

> We focus on when t ≪ 1 and t ≫ 1. From the discussion in Sections 4.2
> and 4.3, we know that the most likely number of particles is either k or k + 1.
> The question we want to address is which one is most likely.

The question is AM-1 of [#18570](https://github.com/the-omega-institute/trureturing/issues/18570).
Write $L=2r\ge4$, $K\ge1$, $0\le k<K$, and $n=(2k+1)r$.
There is an $\varepsilon>0$ such that, whenever $t>0$ and either
$t<\varepsilon$ or $t>1/\varepsilon$, the unique modal occupation is
$k$ if $2k+1<K$, and $k+1$ if $K<2k+1$. If $K=2k+1$, occupations
$k$ and $k+1$ tie and strictly exceed every other occupation in these regimes.

### Statement echo

Lean names in this dossier belong to
`D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (4), $[k]_t=\sum_{j<k}t^j$ | `qnum` | The literal finite sum, including zero at $k=0$. |
| Equation (8), $[k]_t!=\prod_{j<k}[j+1]_t$ | `qfact` | The literal product, including the empty product. |
| Equation (9), the factorial quotient | `qbinom` | The literal quotient for $i\le k$, zero otherwise. |
| Equation (11), steady-state weights | `wt` | The product uses natural exponent $(a^2+2-3a)/2$ with truncated subtraction; its values at $a=0,1,2,3,4$ are $1,0,0,1,3$. |
| Equation (1), configurations | `configs` | Functions $\operatorname{Fin}L\to\operatorname{Fin}(K+1)$ whose natural values sum to $n$. |
| Equation (13), normalized probability | `occProb` | The selected-occupation weight sum divided by the total configuration weight. |
| $L>2$ and half-integer density | `claim`: `r`, `K`, `k`, `hr` | $L=2r$, $r\ge2$, $K\ge1$, $k<K$ and $n=(2k+1)r$. Natural types supply nonnegativity. |
| A site occupation | `claim`: `s` | The first site, the element of $\operatorname{Fin}(2r)$ with value zero. |
| Small and large positive $t$ | `claim`: positive radius and parameter | One radius for both $0<t<\varepsilon$ and $t>1/\varepsilon$. |
| Which adjacent occupation is most likely | `claim`: three conjuncts | Strict comparison with every $b\le K$ outside the stated mode or tied pair. |
| Answer to the question | `result` | The full `claim`, with no additional hypothesis. |

The public definitions follow the binding source conventions of #18570.
They introduce no numerical certificate or experimental premise.

## Motivation

The settling GID is
`D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode.result`.
Its source note is `D5/L/StatisticalMechanics/ayyermisra2024kexclusion`.
The modal comparison distinguishes the two adjacent occupations that share
the ground-state contribution.

## Gap

AM-1 is **Proved** by `result`. Its strict modal classification concerns
the two parameter extremes. A classification at intermediate positive
$t$, and a formal probability-difference asymptotic with its full leading
coefficient, are outside `claim`.

## Route

The proof expresses the source weights through finite occupied-slot sums.
A slot at level $j$ has weight $t^j$. Filling levels below $k$ and choosing
$r$ slots at level $k$ gives ground energy $rk^2$.
Reflection of levels $0,\ldots,2k$ followed by complementation pairs the
adjacent-occupation contributions. Below half filling, the first unmatched
layer has energy $rk^2+k+1$ and excess
$3\binom{2r-1}{r-2}>0$ in favour of $k$.
A finite monomial comparison converts that excess into a strict inequality
for sufficiently small positive $t$. Particle-hole complementation gives
the high-density case and the exact middle tie. Reciprocal invariance of
the marginals transfers the comparisons to large $t$.

These are internal, consumed lemmas of the settling module: the slot
bridge is `occProb_slots`, the excess is `first_unmatched_layer_excess`,
the sign comparison is `unmatched_small_t_adjacent`, the exact tie is
`half_filling_pair`, and reciprocal invariance is `occProb_recip`.

## Falsifier

A permitted triple $(r,K,k)$ and positive parameters approaching zero or
infinity with a different modal ordering would contradict `result`.
A flaw in the slot correspondence, the reflection pairing, or the first
unmatched-layer count would invalidate the explanatory route. A numerical
example at an intermediate parameter does not test the quantified
extreme-regime assertion without a bound on its radius.

## Evidence

The public theorem `result : claim` is kernel-checked. The axiom closure
of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
Every private theorem is a consumed bind-only helper. The public
settlement has `proof_shape: bind-only`, `escape_witness: none`, and
`admission_basis: open-problem-resolution (#18570; Proved)`.
Its direct frozen dependency identities are generated from compiled
proof terms and the producing scoped Lean report in the pull request.

The escape audit of `result` is unfinished under
[#19903](https://github.com/the-omega-institute/trureturing/issues/19903).
The universally quantified, dependent occupation-probability statement
has no completed faithful four-slot registration; no
`declared_validated` registration is claimed.

The [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/65de77d642c949fc7345e8925672d34307a37483/docs/reports/ayyer-misra-2024-kasep-half-density-mode)
contains `check.py`, SHA-256
`981cb87280b7803982fff61a939dc741b7cd3a1513311c7e9bfec4785ddebf9e`.
The command
`python3 /Users/auric/.sshx/b322a84a39ed104bbbb720c0/attempt-1/experiment-check.py`
runs that exact committed script, extracted with
`git -C /Users/auric/trureturing-experiments show 65de77d642c949fc7345e8925672d34307a37483:docs/reports/ayyer-misra-2024-kasep-half-density-mode/check.py`.
Exit code: 0. All 84 triples with $L\in\{4,6,8,10\}$, $1\le K\le6$ and $0\le k<K$ pass the exact-polynomial comparison. The first nonzero numerator-difference coefficient has offset $\min(k+1,K-k)$ above the lowest degree of $Z$, value $\operatorname{sign}(K-2k-1)\,3\binom{L-1}{L/2-2}$, and $Z$ has lowest coefficient $\binom L{L/2}$. The difference is identically zero when $2k+1=K$. At $L=4,K=2,k=1,n=6$, the adjacent numerators are $3+6t+3t^2$ and $3+9t+3t^2$.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Small-$t$ mode below and above half filling | **Proved**, kernel-checked `result`, by the consumed small-parameter comparisons. |
| Large-$t$ mode | **Proved**, kernel-checked `result`; its consumed `occProb_recip` gives reciprocal invariance. |
| Exact middle | **Proved**, consumed kernel-checked `half_filling_pair` gives the adjacent tie for every real $t$; `result` gives dominance over all other occupations in the two extreme regimes. |
| Decisive small-$t$ mechanism | **Proved**, consumed kernel-checked `first_unmatched_layer_excess` gives the positive first unmatched-layer count; `unmatched_small_t_adjacent` gives its strict sign near zero. |
| Uniform parameter scope | **Proved**, kernel-checked `result`: every $r\ge2$, $K\ge1$, $k<K$ and every competing occupation within capacity. No finite parameter enumeration is a premise. |
| Intermediate positive $t$ | **Open**. The strict classification beyond the two extreme regimes is not asserted by `claim`. |
| Full asymptotic probability-difference coefficient and adjacent limit $1/2$ | **Open** as formal corollaries. The layer count motivates these conclusions, but `claim` and `result` do not assert the full normalized asymptotic or the limit. |
| High-density coefficient-index correction | **Computed** in the pinned experiment at the exact scope in Evidence. The first offset is $K-k$, not $k+1$, above half filling; this is not a counterexample to AM-1 and not another settlement. |
| Numerical cross-check of the coefficient mechanism | **Computed** in the pinned experiment at the exact scope in Evidence; this does not prove an unbounded extension. |
| Effect on the source's other conclusions | The mode question is answered in its stated extreme regimes. The high-density coefficient formulation needs the indicated correction; no further source theorem is refuted here. |
| Module placement | One settling module with private consumed helpers. No separate supporting-module admission is asserted. |
| Literature status | The source v2 and the preregistered literature screen report no settlement in their checked scope. Completeness is **ASSUMED-UNVERIFIED**. |

## ASSUMED-UNVERIFIED

The source and literature checks are those recorded by the orchestrator
in #18570. The source v2 Sections 2, 3, 4.5 and 6 were read. The citing
papers arXiv:2401.07999, 2509.05411 and 2510.09191, and later-author
papers including arXiv:2602.17179, are seat-reported literature readings.
This bounded screen does not establish exhaustive citation coverage or
priority. The finite computation does not establish a uniform coefficient
formula or a classification at intermediate positive $t$.
