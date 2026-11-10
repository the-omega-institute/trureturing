---
slug: kotdp-weighteddistinct
bibkey: kotesovec2018weighteddistinct
doi: null
url: https://oeis.org/A022629
triage: theorem
motivation_gids:
  - D5/S0/Asymptotics/GeneratingFunctions/KotesovecA022629.result
---

# Kotesovec's weighted distinct-partition logarithmic limits

## Problem

OEIS A022629 defines $a_1(n)=[x^n]\prod_{k\ge1}(1+kx^k)$ and states:

> Conjecture: log(a(n)) ~ sqrt(n/2) * (log(2*n) - 2).

The coefficient index ranges over every natural number, including zero. The claim means that the quotient tends to one along all natural indices. For a positive natural exponent $r$, write
$a_r(n)=[x^n]\prod_{k\ge1}(1+k^r x^k)$.
The related entries A092484, A265840, A265841 and A265842 take $r=2,3,4,5$, respectively. Their denominators are $\sqrt{2n}(\log(2n)-2)$ for $r=2$, and $r\sqrt{n/2}(\log(2n)-2)$ for $r=3,4,5$.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| A022629: “Expansion of Product_{m>=1} (1 + m*q^m).” | `KotesovecA022629.a` | The coefficient of degree $n$ in factors $1$ through $n$; later factors cannot affect that coefficient. |
| A022629: the quoted conjecture | `KotesovecA022629.claim`, `KotesovecA022629.result` | Exact source denominator; no assumed positivity or asymptotic hypothesis. |
| A092484: “Expansion of Product_{m>=1} (1 + m^2*q^m).” and its logarithmic conjecture | `KotesovecA092484.a`, `.claim`, `.result` | The literal $r=2$ normalization. |
| A265840, A265841, A265842: products with exponents $3,4,5$ and their logarithmic conjectures | The corresponding modules' `a`, `claim`, `result` | Each source denominator is retained. |
| Natural indices, including zero | Each `a` has domain $\mathbb N$ | Total real logarithm and division affect only initial exceptional indices. |
| Every fixed positive natural exponent | `KotesovecA022629.all_exponents` | A consumed family theorem; fixing $r$ introduces no additional hypothesis into the five source claims. |

All Lean names above have prefix `D5.S0.Asymptotics.GeneratingFunctions`. The coefficient expression and the triangular sum are inline where needed; no higher-stratum triangular-number definition is imported.

## Motivation

The settling declaration is `D5/S0/Asymptotics/GeneratingFunctions/KotesovecA022629.result`, under external named open-problem admission #21434 (Proved). The adjacent named claims are preregistered in #21435, #21436, #21438 and #21439. The source definitions and attributions are in [the Library note](../Library/Asymptotics/kotesovec2018weighteddistinct.md).

## Gap

The source conjectures ask for ratio asymptotics of the actual coefficient sequences. An upper bound alone or a computation on finitely many coefficients cannot prove those limits. A lower contribution with the same leading logarithmic rate and an error negligible relative to that rate are required.

## Route

Let $D_n$ consist of subsets of $\{1,\ldots,n\}$ whose elements sum to $n$, and let $P(S)$ be the product of the elements of $S$. Polynomial expansion gives
$a_r(n)=\sum_{S\in D_n}P(S)^r$.
A nearly triangular partition contributes at least $(M!)^r$, where $M$ is maximal with $M(M+1)/2\le n$. The logarithm of $|D_n|$ is at most $2\sqrt n$. Bounding each partition product and combining these two estimates gives the finite sandwich used by the ratio-limit proof.

## Falsifier

A failure of the exact natural-index quotient limit would refute the corresponding source conjecture. A finite coefficient mismatch would instead refute the coefficient interpretation. A missing additive second term or prefactor does not refute a ratio limit. No finite computation here certifies an infinite limit.

## Evidence

### Mathematical evidence

The five `result` declarations prove their literal `claim` definitions. `KotesovecA022629.all_exponents` proves the fixed-positive-natural-exponent family. The private declarations `factorial_witness`, `count_log_bound` and `weighted_distinct_subset_log_sandwich` supply the corresponding finite inequalities. All mathematical modules import pinned Mathlib; the four adjacent modules additionally import the A022629 owner.

### Finite computation

The experiment is [the weighted distinct-partition checker](https://github.com/the-omega-institute/trureturing-experiments/tree/53f0db6627014ac92ef1aa24517b52fc338485c9/docs/reports/kotesovec-weighted-distinct-partition-log-asymptotics).
At that immutable revision, `check.py` has SHA-256 `efe81d3bf65c873ebd289891ca08dab21a666e6af396ae5f4cc329a70c04b2bf`.
Command: `python3 check.py`; exit code 0; final result `ALL_CHECKS_OK`.
The checked scope is all 43/31/29/26/23 supplied terms for the five entries and both degree-six examples; independent enumeration through $n=45$ (16,857 distinct partitions); exact integer bounds for $n=1,\ldots,180$, $r=1,\ldots,5$; and rational logarithmic sandwiches for $n=2,\ldots,180$, $r=1,\ldots,5$. The logarithm enclosures use 48 positive atanh-series terms with a geometric tail; square roots use integer `isqrt`. These computed claims have only that finite scope.

### Escape audit

The audit is unfinished: [#21754](https://github.com/the-omega-institute/trureturing/issues/21754) names all six public theorem targets. No faithful filter-limit reconstruction, whole-family intervention/sensitivity proof and observational-dependence bridge is supplied by the available specialized registrations. No Reg registration or `declared_validated` status is claimed.

## Triage

| Item | Status and evidence kind | Boundary |
| --- | --- | --- |
| All five literal claims and the fixed-natural-exponent family theorem | **Proved, kernel-checked:** the five modules' `result` declarations and `KotesovecA022629.all_exponents`. | Every fixed natural $r\ge1$; no uniform variable-exponent limit theorem. |
| Nearly triangular product at least $(\operatorname{index} n)!$ and $\log q(n)\le2\sqrt n$; finite sandwich and $O_r(\sqrt n)$ error | **Proved:** the first three finite statements are kernel-checked by `factorial_witness`, `count_log_bound`, `weighted_distinct_subset_log_sandwich`; the error conclusion is derived below in prose. | The sandwich holds for every natural $r\ge1$ and $n\ge2$. |
| Supplied finite checker | **Computed:** the immutable experiment, command, exit code and SHA-256 in Evidence. | `ALL_CHECKS_OK` over exactly the finite ranges above. |
| Sharper additive second term, prefactor, positive nonintegral exponents, separate variable-exponent limit theorem | **Open.** | The finite sandwich is uniform for natural $r\ge1$ with constants affine in $r$; that is not a variable-exponent limit result. |
| Complete prior-art and priority determination | **Open; literature completeness ASSUMED-UNVERIFIED.** | Only the successfully read literature scope below is covered. |

### What the settlement shows

Put $R=\sqrt{2n}$ and $B_r(n)=rR(\log R-1)$. The finite sandwich is
$$
B_r(n)-2r\log R-r\le\log a_r(n)
\le B_r(n)+rR(2-\log2)+2\sqrt n.
$$
For $n\ge2$, $R\ge1$, $\log R\le R$, $1\le R$, $\log2\ge0$, and $\sqrt n\le R$. The lower error is at most $3rR$ and the upper error at most $(2r+2)R$. Therefore
$$
|\log a_r(n)-B_r(n)|\le(3r+2)\sqrt{2n}.
$$
This is a **proof in prose from the kernel-checked finite sandwich**, not a separately named public Lean theorem. Its constants are affine in the natural exponent. Dividing by $B_r(n)$ for fixed $r\ge1$ makes the relative error vanish, since $\log R\to\infty$. One nearly triangular partition supplies the leading rate; counting all distinct partitions changes its logarithm only at the smaller $\sqrt n$ scale.

The argument settles the four adjacent source ratios through their named `result` declarations. It does not isolate the coefficient of an additive $\sqrt n$ term: the available error is itself of that order. The classical exact maximum-product partition is not asserted as a new theorem. No result in the source entries is stated as conditional on these conjectures; no downstream source theorem is claimed to change. Additive asymptotics, prefactors, positive nonintegral exponents and variable-exponent limits remain follow-up questions.

### Literature status

The bounded literature reading in #21434 found no verified settlement in its successfully read scope. Schneider–Sills, arXiv:1904.08004v2, states Došlić's classical distinct-part maximum norm and Lehmer's inverse-norm results. The 2025 Rana–Kaur–Kumar paper, NNTDM 31(4), 908–915, defines the same first product and gives recurrences, without the target logarithmic limit. Bridges–Craig, arXiv:2308.00123, Theorem 1.1 concerns unrestricted partitions and reciprocal products, whose exponential scale differs. Kumar–Rana, DOI `10.1007/s11139-026-01350-4`, was read only through its abstract, references and exposed appendices; the main text was not read. Its sufficiency for a distinct-part moment bound remains unverified. Bounded author, metadata and citation searches do not establish absence of prior work. The literature synthesis and priority remain ASSUMED-UNVERIFIED.

## ASSUMED-UNVERIFIED

Literature completeness and priority are not established. The unread main text of DOI `10.1007/s11139-026-01350-4`, unread originals underlying some survey quotations, incomplete citation access and bounded author searches remain material limits. Equality of retrieved arXiv texts to journal versions is not claimed. Finite computations certify only their tested scope. Escape registration remains unfinished under #21754; the mathematical proof does not supply the missing audit bridge.
