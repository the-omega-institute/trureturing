---
slug: zhu-2024-clifford-third-moment-sigma-lower-bounds
bibkey: zhu2024thirdmoments
doi: 10.48550/arXiv.2410.13575
url: https://arxiv.org/abs/2410.13575v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.result
---

# At dimension five the full and non-symmetric aggregates of a two-qudit state fall below their conjectured lower bounds

## Problem

H. Zhu, C. Mao and C. Yi, *Third moments of qudit Clifford orbits and 3-designs based on magic
orbits*, arXiv:2410.13575v1, Section VII.1, Conjecture 2, asserts for an odd prime $d$ and
$|\Psi\rangle\in\mathcal H_d^{\otimes n}$ the pointwise bounds $0\le\kappa(\Psi,\mathcal T)\le1$ on
$\Sigma(d)$ together with the aggregate bounds $6\le\kappa(\Psi,\Sigma(d))\le2d+2$,
$0\le\kappa(\Psi,\mathscr T_{\rm ns})\le2d-4$ and $\kappa(\Psi,\mathscr T_{\rm iso})\ge6$. Here
$\Sigma(d)$ is the set of stochastic Lagrangian subspaces of $\mathbb F_d^6$,
$\mathscr T_{\rm sym}=\{\mathcal T_O\mid O\in S_3\}$, $\mathscr T_{\rm ns}=\Sigma(d)\setminus\mathscr T_{\rm sym}$
and $\kappa(\Psi,\mathscr T)=\sum_{\mathcal T\in\mathscr T}\kappa(\Psi,\mathcal T)$. The verbatim statements are in
[the literature note](../Library/QuantumStates/zhu2024thirdmoments.md).
The pointwise clause and the clause $\kappa(\Psi,\mathscr T_{\rm iso})\ge6$ are refuted
([pointwise](zhu-2024-clifford-third-moment-kappa-negativity.md),
[isotropic aggregate](zhu-2024-clifford-third-moment-aggregate-lower-bound.md)). Issue
[#14620](https://github.com/the-omega-institute/trureturing/issues/14620) targets the two remaining lower
bounds, $6\le\kappa(\Psi,\Sigma(d))$ and $0\le\kappa(\Psi,\mathscr T_{\rm ns})$.

## Motivation

The paper uses the aggregate sums over $\Sigma(d)$ for the shadow norms of stabilizer projectors and
for the third frame potential of Clifford orbits, and derives the aggregate bounds from the pointwise
clause. Whether the lower bounds over $\Sigma(d)$ and $\mathscr T_{\rm ns}$ hold decides whether the
consequences stated with them survive the failure of the pointwise clause.

## Gap

The paper proves $4(D+d)/(D+1)\le\kappa(\Psi,\Sigma(d))$ with $D=d^n$, which is at least $6$ only for one
qudit, the upper bounds, and the conjecture for $d=3$. It states $|\Sigma(d)|=2d+2$ and, for
$d\equiv2\pmod3$, $\Sigma(d)=\mathscr T_{\rm iso}$. Issues #14561 and #14620 record the literature
checks before any Lean: no later work proves or refutes the aggregate lower bounds;
`not-found-in-searched-scope`.

## Route

Let $\mathcal T\in\Sigma(5)$ and $(\mathbf 0;\mathbf y)\in\mathcal T$. The quadratic condition gives
$\mathbf y\cdot\mathbf y=0$, and applied to $(\mathbf 1;\mathbf 1+\mathbf y)$ it gives $\sum_ky_k=0$. Then
$\mathbf y\cdot\mathbf y=2(y_1^2+y_1y_2+y_2^2)$ with $-3$ a non-square mod $5$, so $\mathbf y=\mathbf 0$. The
second projection is injective on the three-dimensional $\mathcal T$, so $\mathcal T=\mathcal T_O$, and
the conditions make $O$ a stochastic isometry. Hence $\Sigma(5)=\mathscr T_{\rm iso}$. For the
two-qudit state $\Psi=v/\sqrt{458}$ of #14561, $\kappa(\Psi,\Sigma(5))=140241723/24017978<6$; each of
the six permutation graphs has $\kappa=1$, so
$\kappa(\Psi,\mathscr T_{\rm ns})=-3866145/24017978<0$.

## Falsifier

An error in the classification $\Sigma(5)=\mathscr T_{\rm iso}$, in the identification of
$\mathscr T_{\rm sym}$ or in the frozen two-qudit values. Exhaustive enumeration gives
$|\Sigma(5)|=12$ with every element a graph, as the paper's $|\Sigma(d)|=2d+2$ requires.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.lean`, with public
`claim` (the disjunction of the two lower bounds) and `result : ¬ claim`. The axiom closure of
`result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`,
`native_decide` or new axiom. The module statement is `sha256:5e69691622247a60b0dfb251155c7bb412574c1cc80d163011458f6d54241347`, the
`result` statement `sha256:52e7406bf235904808230d3d5fff4d7ac140f9f5b981894bd6f29778a06569a9`, the `claim`
statement `sha256:969abd3b9602def77f7e1d6cd9ab6c13cc157b41fed903c3260da2c5616ad9e4` and the
`sigmaSubspaces_five` statement `sha256:e3df810a9f40214791e9c8732254144d2673d6f3c4fedfadfccb5ac5b40c2618`. The Freeze
event is `sha256:c61cb9bb0f116f6787b705cd355848bd4436e40572e8886a161ff79dd10358b2`; its one project-level
prerequisite is the frozen node `sha256:0630d507568cef406b80d8acc31aaccdd8f6709e5874320aff894907aa780a56` of
`D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation`, whose graph subspaces, $O_3(d)$,
$\mathscr T_{\rm iso}$, state and values the module reuses; `IsStochasticLagrangian` and `kappa` come from
`D5/S3/Quantum/Magic/CliffordThirdMomentNegativity`.

## Triage

Tier 1 printed clauses of an October 2024 conjecture, preregistered in issue #14620 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | sigmaSubspaces_five | open-problem-resolution |

Content declarations, each on the live proof of `result`: the public classification
`sigmaSubspaces_five` ($\Sigma(5)=\mathscr T_{\rm iso}$), the private kernel fact that no nonzero
$\mathbf y\in\mathbb F_5^3$ has $\mathbf y\cdot\mathbf y=0=\sum_ky_k$, the two lemmas that turn it into the
graph description, and the values `kappa_sigma_five` and `kappa_ns_five`. The bind-only private lemma
`graph_stochastic` (every $\mathcal T_O$ with $O\in O_3(d)$ satisfies the three conditions) is used by
the classification and by `kappa_ns_five`. The settlement is admitted as an external open-problem
resolution.

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the refutation shows

**Proved by `result`:** both lower bounds $6\le\kappa(\Psi,\Sigma(d))$ and
$0\le\kappa(\Psi,\mathscr T_{\rm ns})$ of Conjecture 2 fail for a normalized two-qudit state at $d=5$.
Together with the earlier refutations, every lower bound of Conjecture 2 fails; the upper bounds are
the paper's theorems.

**Argued, not formalized.**
- *Every $n\ge2$.* Graph expectations are multiplicative under tensor products and equal $1$ for a
  stabilizer state, so $\Psi\otimes|0\rangle^{\otimes(n-2)}$ has the same values.
- *Primes $d\equiv2\pmod3$.* The argument for $\Sigma(5)=\mathscr T_{\rm iso}$ uses only that $-3$ is
  a non-square mod $d$, which holds exactly for $d\equiv2\pmod3$; it agrees with the paper's statement
  for those primes.

**Open.** Whether the lower bounds over $\Sigma(d)$ hold for two qudits at $d\equiv1\pmod3$, where
$\Sigma(d)$ contains four defect subspaces besides $\mathscr T_{\rm iso}$; the exact minimum of
$\kappa(\Psi,\Sigma(d))$ for $n\ge2$.
