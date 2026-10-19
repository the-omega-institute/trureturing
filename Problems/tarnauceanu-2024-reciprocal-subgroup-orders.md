---
slug: tarnauceanu-2024-reciprocal-subgroup-orders
bibkey: tarnauceanu2024reciprocal
doi: null
url: https://www.math.uaic.ro/~martar/pdf/articole/articol%20141.pdf
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders.result
---

# Tărnăuceanu's reciprocal subgroup-order conjecture

## Problem

Marius Tărnăuceanu, *On the sum of inverses of subgroup orders in finite groups*,
Scientific Studies and Research, Series Mathematics and Informatics 34 (2024),
no. 1, 115–120, printed p. 119, Conjecture 3.1:

> There is no constant c > 1 such that f(G) > c, for all finite non-cyclic groups G.

On printed p. 116 the source defines:

> In the current note, we consider the function f(G) = Σ_{H∈L(G)} 1/|H|.

Here $L(G)$ is the whole subgroup lattice, including the trivial and full subgroups.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Sum of reciprocal subgroup orders | `f` | `finsum` over `Subgroup G`, with real reciprocal of `Nat.card H`; for finite groups this is a finite sum. |
| No constant $c>1$ | `claim` | Negated existential over real $c$, retaining the strict inequality. |
| All finite non-cyclic groups | `claim` | Every `G : Type`, its group and finite instances, and the hypothesis `¬ IsCyclic G`. Every finite group has such a carrier up to isomorphism. |
| $f(G)>c$ | `claim` | Exactly the strict inequality `c < f G`. |
| Conjecture holds | `result` | The complete proposition `claim`, with no extra hypothesis. |

The definitions are the literal conventions in preregistration
[#18701](https://github.com/the-omega-institute/trureturing/issues/18701).

## Motivation

The source proves a conditional construction using infinitely many Sophie Germain
primes. Allowing the cyclic complement's exponent to increase removes that hypothesis.
The settlement concerns the reciprocal subgroup-order sum, rather than the element-order
sum or the subgroup conjugacy ratio.

## Gap

Conjecture 3.1 is an externally published named question. The source's conclusion is
conditional on the Sophie Germain conjecture. The literature screen recorded in #18701
found no unconditional settlement; its completeness is `ASSUMED-UNVERIFIED`.

## Route

`D5.S3.FiniteGroups.TarnauceanuReciprocalSubgroupOrders.result` proves `claim`.
Choose a large prime $q$, a prime $p>q$ with $p\equiv1\pmod q$, and then $s>0$.
The imported `CyclicPrimePowerAction.actionData` and `SplitGroup` construct the
actual split group $C_p\rtimes C_{q^s}$. The private `split_not_cyclic` proves
non-cyclicity. The private `split_sum_bound` obtains

$$
f(G)\le\frac1p\frac q{q-1}+\frac q{q-1}+\frac p{q^s}.
$$

The proof uses `CyclicPrimePowerAction.subgroupEnumeration`, `cyclicSubgroupEquiv`,
`cyclic_card` and `kernel_power_card`. Mathlib's
`Nat.exists_prime_gt_modEq_one` supplies $p$ without a Sophie Germain hypothesis.
`geom_sum_Ico_le_of_lt_one` supplies the geometric estimate and
`pow_unbounded_of_one_lt` supplies a sufficiently large exponent.
Each helper has a consumer in the settling proof; `proof_shape` is `bind-only`.
Admission is `open-problem-resolution (#18701; Proved)`, generality is `G`,
and utility is `none`: the delivered argument is symbolic, with no finite numerical
certificate as mathematical content.

## Falsifier

A subgroup missing from the imported enumeration, an incorrect cardinality for one of
its cases, or a failure of the displayed estimate would invalidate this route.
The exact Lean result is checked with axiom closure contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Evidence

The source note is [tarnauceanu2024reciprocal](../Library/FiniteGroups/tarnauceanu2024reciprocal.md).
The public mathematical sources are the settling module and its Blueprint Scribe,
and the two cardinality declarations published in the existing frozen owner.
Escape audit is unfinished for `result`, `CyclicPrimePowerAction.cyclic_card`
and `CyclicPrimePowerAction.kernel_power_card`: [#19077](https://github.com/the-omega-institute/trureturing/issues/19077).
No completed four-slot registration is asserted.

### Experiment

[Reproducible subgroup enumeration and family checks](https://github.com/the-omega-institute/trureturing-experiments/tree/ccbaf989021fa46a59db4ff7a3c1a96976bae8d3/docs/reports/tarnauceanu-2024-conjecture-3-1-reciprocal-subgroup-orders),
commit `ccbaf989021fa46a59db4ff7a3c1a96976bae8d3`.
Command: `python3 check.py` in that pinned directory; exit 0, `RESULT PASS`.
Script SHA-256: `4f9f06ff124320fd44b3a4e9fe5ae8e748ad93afa58ae892f40e2eccd914ae4d`.
The script bytes were checked against that Git object before execution.

Computed scope: all subgroups of the five split groups with
$(p,q,s)=(7,3,1),(7,3,2),(5,2,3),(13,3,2),(11,5,1)$.
Their counts are respectively $10,12,12,18,14$, and their exact reciprocal sums
are $74/21,146/63,11/4,26/9,182/55$. Each agrees with the formula below and
is nonabelian. For $q=3,5,11,23,47,101$, with $p$ the least prime congruent to
one modulo $q$ and $s$ the least exponent with $p/q^s<1/q$, the formula satisfies
$1<f(G)<1+3/(q-1)$. The corresponding $p$ are $7,11,23,47,283,607$ and every
selected exponent is $3$. The experiment verifies precisely these finite cases;
it is not the evidence for the universal theorem.

## Triage

### What the settlement shows

- **Settlement — kernel-checked.** `result` proves the exact binding `claim`, with
  no Sophie Germain assumption. It negates the existence of a strict universal
  lower bound above one.
- **Mechanism — proved in prose from the bound used in `result`.** With $p>q$,
  the first term of the displayed bound is at most $1/(q-1)$ and its middle term
  is $1+1/(q-1)$. Choose $q$ with $3/(q-1)<c-1$, then choose $p$, then $s$ with
  $p/q^s<1/(q-1)$. Thus $f(G)<c$. The live Lean proof performs this parameter
  selection using the elementary cyclotomic prime supplier
  `Nat.exists_prime_gt_modEq_one` and the power-unboundedness theorem.
- **Scope and nonattainment — proved in prose; no additional exported Lean theorem.**
  Every finite nontrivial group has distinct trivial and full subgroups. Their
  contributions are $1$ and $1/|G|$, and all other contributions are nonnegative.
  Hence $f(G)\ge1+1/|G|>1$. Together with the arbitrary-threshold construction,
  this gives infimum $1$ on finite non-cyclic groups, with no minimizer. The
  kernel-checked public theorem is exactly `claim`; the lower bound and infimum
  wording here include this additional prose argument.
- **Issue correction — proved in prose.** For the trivial group the trivial and
  full subgroups coincide and $f(G)=1$. The bound $1+1/|G|$ therefore requires
  nontriviality. A non-cyclic finite group is nontrivial, so the correction
  leaves the conjecture and the supplied family unchanged.
- **Exact truncated formula — proved in prose from the imported enumeration;
  no named theorem exported here.** The inverse-image subgroups have orders
  $pq^j$ for $0\le j\le s$; the proper embedded quotient subgroups have orders
  $q^j$ for $0\le j<s$; and the $p$ conjugate complements have order $q^s$.
  Reweighting these disjoint exhaustive cases gives

  $$
  f(G)=\sum_{j=0}^s\frac1{pq^j}
       +\sum_{j=0}^{s-1}\frac1{q^j}+\frac p{q^s}.
  $$

- **Minimal non-cyclic family — proved in prose; not formalized as a theorem here.**
  The proper embedded quotient subgroups and complement conjugates are cyclic.
  A proper inverse-image subgroup has order $pq^j$ with $j<s$. The action
  factors through the quotient of order $q$, so its restriction to this
  subgroup of $C_{q^s}$ is trivial. The inverse image is therefore
  $C_p\times C_{q^j}$, cyclic because the factor orders are coprime. The
  enumeration exhausts all proper subgroups. Thus the same construction gives
  infimum $1$ even when all proper subgroups are required to be cyclic.
- **Family lower rate — proved in prose.** For $s>0$ the group has a subgroup
  of order $q$, distinct from the trivial subgroup (a proper embedded subgroup
  when $s>1$, a complement when $s=1$). Their two contributions give
  $f(G)-1\ge1/q$ uniformly in $s$. This is not a named exported Lean theorem.
- **Optimal growth — open.** No optimal bound in terms of the group order is
  established for $\inf\{f(G):G\text{ finite non-cyclic},\ |G|\le N\}$.
  The fixed-parameter experimental values above do not settle this question.
- **Literature — literature reading.** #18701 records the source's Theorem 1.1,
  Corollary 1.3 and Section 3 as read by the orchestrator. The author's index,
  the earlier normal-subgroup analogue and related ZM-group papers were reported
  by the search seat; those reports do not establish completeness. No source
  theorem dependent on the conjecture is re-proved here. Its conditional
  conclusion about Conjecture 3.1 is made unconditional by `result`.

The exact formula, minimal non-cyclicity, nonattainment and order-dependent rates
are not additional Lean theorems in this delivery. The finite numerical values
are computed evidence only. The literature screen found no unconditional answer
in its inspected scope, including the repository and formal-conjectures search
recorded in #18701.

## ASSUMED-UNVERIFIED

Completeness of the literature search, priority of the unconditional observation,
and any optimal rate as a function of group order are unverified. The template-specific
source reconstruction and variation/sensitivity evidence for the three audit targets
is unfinished. These boundaries do not add hypotheses to `claim` or `result`.
