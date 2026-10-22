---
slug: miska-ulas-2022-sigma-three-conjecture-4-8
bibkey: miskaulas2022sigma
doi: 10.1142/S1793042124500635
url: https://arxiv.org/abs/2203.03942v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/MiskaUlasSigmaThreeBound.result
---

# Refutation of Miska–Ulas Conjecture 4.8

## Problem

Miska and Ulas, *On the Diophantine equation σ₂(X̄ₙ) = σₙ(X̄ₙ)*, arXiv:2203.03942v1, page 16, Conjecture 4.8 states:

> Let n ∈ N≥4 and suppose that m ∈ N satisfies m = σ_3(X_n) = σ_n(X_n). Then m ≤ (1/12)(3021n⁶ − 77575n⁵ + 920361n⁴ − 6235705n³ + 24764202n² − 53664304n + 48986640) and x_n ≤ (1/12)(27n⁴ − 190n³ + 471n² − 500n + 216).

Write $Q(n)$ and $D(n)$ for the two bounds, respectively. The source defines $\sigma_j$ as the elementary symmetric sum of products over $j$ distinct increasing indices, and a solution as a nondecreasing tuple of positive integers. The target is the conjunction as printed in version 1. Preregistration: [#19678](https://github.com/the-omega-institute/trureturing/issues/19678).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $n\ge4$ | `claim` quantifies `n : ℕ` with `hn : 4 ≤ n` | Exact |
| Positive integer tuple $X_n$ | `X : Fin n → ℕ` and positive entries | Exact; zero-based indices |
| $x_i\le x_{i+1}$ | `Monotone X` | Equivalent on the finite linear order |
| $m=\sigma_3(X_n)=\sigma_n(X_n)$ | Both equalities to `MvPolynomial.eval X (MvPolynomial.esymm (Fin n) ℕ j)` | Literal subset-product sum; no new symmetric-sum alias |
| $m\le Q(n)$ and $x_n\le D(n)$ | The two rational inequalities in `claim`; last entry indexed by `n - 1` | Both conjuncts retained |
| Refutation | `result : ¬ claim` | The first conjunct fails at $n=11$ |

The rational casts preserve the integer inequalities and interpret the source's factor $1/12$ exactly. The index proof follows from $n\ge4$ and adds no mathematical hypothesis.

## Motivation

For $k=n-4$, set $c=3\binom{k}{2}+8k+7=(k+2)(3k+7)/2$ and $Y=(1^k,2,k+3,c)$. Let $d=\sigma_3(Y)$ and append $d$ to obtain $X_n$. The product $P=2(k+3)c$ satisfies $\sigma_2(Y)+1=P$. Hence
$\sigma_3(X_n)=d+d\sigma_2(Y)=dP=\sigma_n(X_n)$.
The family preserves positivity and order and violates the first proposed bound for every $n\ge11$.

## Gap

The universal coordinate bound $x_n\le D(n)$ remains open: the displayed family attains equality. A degree-seven or larger replacement bound for all solutions is also open. The journal publication metadata is verified, but its full text and whether it retains Conjecture 4.8 are unverified. No publication-priority claim is made.

## Route

The settling module imports only pinned Mathlib. `MvPolynomial.aeval_esymm_eq_multiset_esymm` supplies the symmetric-sum correspondence. Multiset expansion, binomial coefficient identities, and polynomial normalization give the family, its domain conditions and its factored gap. The public theorem specializes the private `family` at $k=7$ and contradicts the first conjunct of `claim`.

The form is `deposit-uncovered` (no atom), settling `D5/S3/Arith/MiskaUlasSigmaThreeBound.result`. The module's admission basis is `open-problem-resolution (#19678; Refuted)`; every delivered declaration has `proof_shape: bind-only`, `escape_witness: none`, and no direct frozen D5 dependency. Private helpers are consumed within the settlement. Their compiled dependency map supplies the named consumers; no independent general-content result is asserted.

## Falsifier

A proof of the printed universal conjunction would apply to the positive nondecreasing tuple at $n=11$ and force $40766040\le40732020$, contradicting `result`. The refutation concerns the quoted conjunction, not the universal truth or falsity of its second conjunct.

## Evidence

- Kernel evidence: `D5/S3/Arith/MiskaUlasSigmaThreeBound.lean`, public `claim` and `result`; the private `family`, `xvals_domain`, `xvals_solution`, `product_gap`, `product_exceeds`, and `dval_cast` supply the internal argument.
- Canonical mirror: `Blueprint/D5/S3/Arith/MiskaUlasSigmaThreeBound.scribe.cs`; its result has one Refuted resolution claim for this dossier.
- Source: `Library/ArithUnits/miskaulas2022sigma.md`.
- The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
- Experiment: [exact family checks](https://github.com/the-omega-institute/trureturing-experiments/tree/6093429385079a7ceb59fdebbfa0ada25e88047f/docs/reports/miska-ulas-2022-sigma-three-conjecture-4-8). Command: `python3 /Users/auric/trureturing-experiments/docs/reports/miska-ulas-2022-sigma-three-conjecture-4-8/check.py`, whose bytes match that pinned commit; exit 0. Script SHA-256: `dfcb47cf22e6f66796b5d520e24886ec6331a4b6ad39cea6770419bbc0791d81`. Exact tested scope: every integer $4\le n\le200$. The checks establish tuple length, positivity, order, $\sigma_3=\sigma_n$, $x_n=D(n)$, the factored gap, and strict excess exactly for $n\ge11$ within that finite range.

## Triage

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| The printed conjunction is false | **Proved, kernel-checked:** public `result` | Version-1 Conjecture 4.8; one counterexample suffices |
| First bound fails for every $n\ge11$ | **Proved using the internal kernel argument:** private `family` and `product_exceeds`, with $k=n-4$ | Every natural $n\ge11$; not a separate public theorem |
| Explicit tuple and exact values | **Computed:** the experiment above | $X_{11}=(1,1,1,1,1,1,1,2,10,126,16177)$; $\sigma_3=\sigma_{11}=40766040$, $Q(11)=40732020$, difference $34020$ |
| Degree-seven failure mechanism and interpolation | **Proved in prose:** the factorization below, also the internal identity `product_gap` | All $n\ge4$ on this family; no assertion about how the authors chose $Q$ |
| Family attains the second bound | **Proved, kernel-checked internally:** `dval_cast` | $d=D(n)$ for this family |
| Universal second bound | **Open** | The family does not refute $x_n\le D(n)$ for all solutions |
| Universal replacement bound of degree at least seven | **Open** | This family imposes a growth constraint; it proves no universal upper bound |
| Source's other results | **Literature reading:** Sections 1–4 as recorded in #19678 | The proved results about $\sigma_2=\sigma_n$ concern a different equation; this refutation supplies no counterexample to them. Extending those results to $\sigma_3$ remains open |
| Publication priority; unchanged journal wording; independent general new content | **Open / unclaimed** | Literature completeness is `ASSUMED-UNVERIFIED`; no independent generic-content theorem is delivered |

The factored gap is
$$m_n-Q(n)=\frac{27}{4}\prod_{j=4}^{10}(n-j).$$
Its seven factors show positivity for $n\ge11$ and vanishing at the seven distinct integers $4,\ldots,10$. Since $m_n=2(n-1)cD(n)$ has degree seven with leading coefficient $27/4$, while $Q$ has degree at most six, $Q$ is the unique degree-at-most-six interpolant of this family's values at those seven points. This algebraic explanation does not identify the authors' numerical search range or their method of choosing $Q$. The family is compatible with a sharp universal second bound, whose proof remains open.

### Declaration judgement

Every definition and theorem has `proof_shape: bind-only`; no same-delivery content declaration or escape witness occurs. The public judgement is:

| module | declaration | proof_shape | escape_witness | consumers | direct frozen dependencies |
| --- | --- | --- | --- | --- | --- |
| `D5/S3/Arith/MiskaUlasSigmaThreeBound` | `D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.result`; declaration statement_id `sha256:827d21c9f074bfa12c788eb607145c21ff8f06d718f52187a8f741bae44c3651` | bind-only | none | designated settlement | none |

| helper (full compiled name) | proof_shape | direct consumer(s) |
| --- | --- | --- |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.sigma_multiset` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.esymm_cons` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.appended_solution`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.defect_one`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_expand` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.esymm_replicate` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.cval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.defect_one`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_expand` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.cval` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.appended_solution`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.cval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.defect_one`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_expand`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_ge`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_gap`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.pval`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_domain`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_multiset`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.yvals` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.yvals` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.appended_solution`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.defect_one`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_expand`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_ge`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_exceeds`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_gap`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_domain`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_multiset`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.pval` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.appended_solution`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.defect_one`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_expand`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_ge`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_exceeds`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_gap`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_domain`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.defect_one` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.appended_solution` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_expand` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_ge` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_ge` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_domain` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.cval_cast` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_cast`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_gap` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.dval_cast` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_gap` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.appended_solution` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals` | bind-only | `D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.result`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_domain`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_multiset`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_multiset` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_domain` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.xvals_solution` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.qbound` | bind-only | `D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.result`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_exceeds`; `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_gap` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_gap` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_exceeds` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.product_exceeds` | bind-only | `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family` |
| `_private.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.0.D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.family` | bind-only | `D5.S0.Certificates.Polynomials.MiskaUlasSigmaThreeBound.result` |

The module admission basis is `open-problem-resolution (#19678; Refuted)`. This classification reports normalization and consumed helper applications; it does not weaken the settlement of the externally named conjecture.

## ASSUMED-UNVERIFIED

Literature completeness and continued prior-art openness are `ASSUMED-UNVERIFIED`. The source screen recorded in #19678 covers arXiv's version record, title/identifier/author searches, indexed later works and the formal-conjectures archive; it found no matching settlement in that searched scope. The journal PDF was inaccessible, and exhaustive later-literature coverage and publication priority are unverified. The result refutes the quoted version-1 statement. Finite experiment checks do not by themselves establish any uniform unbounded conclusion.
