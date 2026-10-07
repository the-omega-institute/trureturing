---
bibkey: segovia2026partitions
authors: Carlos Segovia
year: 2026
title: The Riemann Hypothesis through the looking of partitions
doi: null
url: https://arxiv.org/abs/2601.22413v3
claim: The preprint studies Espinosa partition branches and reports a rigorous first branch plus conditional/computational higher-branch evidence; it does not provide a FIB source map or an unconditional RH proof.
strata_touched: []
license: citation-only
triage: anchor
---

# Espinosa branches and integer partitions

The source is Carlos Segovia, [arXiv:2601.22413v3](https://arxiv.org/abs/2601.22413), updated 1 September 2026. It was not independently formalized here.

The paper decomposes an Espinosa-type RH-equivalent inequality into partition branches $A_r(n)$, proves the first branch, computes asymptotic branch proportions and the hook-family contribution, and uses the Alaoglu--Erdős conjecture together with a finite CA list to report the first seven higher-branch cutoff realizations. The latter are conditional/computational evidence, not an unconditional RH result.

The partition index $r$ counts a branch in a symmetric-polynomial expansion. It is not the FIB five-window state, the Fibonacci rank, or a bound on $\omega(n)$. Consequently the source offers a different decomposition of the same Robin budget but no map from

$$
[null,2,3,2\,5,5]
$$

to its divisor subsets. Reusing its branch asymptotics would require a new common-source and pointwise realization theorem.

## Exact scope of the first divisor realization

The versioned [primary PDF](https://arxiv.org/pdf/2601.22413v3) has 19 pages
and SHA-256 `8ce22ded9964d81c5742d39235f85f310be0ab013f637a946b3c5517db6cd239`.
The locators below identify inspected source statements and conditions;
they do not certify every proof or supply Lean verification.

Equation (11), printed p.3, repeated as (85), p.15, uses the stated domain
of positive nonsquare integers with sufficiently many divisors. It orders
$1=d_1<\cdots<d_{\tau(N)}=N$, puts $S_r=\sum_{i=1}^r\rho_i$, and defines

$$
d^{(r)}(N)=\max\left\{d_j:
\sum_{i=1}^j\frac{N}{d_i}\le S_rN\log\log N\right\}.
$$

The cutoff is the actual divisor value $d_j$, while the prefix sum is
indexed by $j$. Its budget inequality is part of the definition. The
source states on p.3 that saturation $d^{(r)}(N)=N$ is equivalent to
$Z(N)\le S_r\log\log N$; defining the cutoff does not prove saturation
or bound the omitted divisor response.

Lemma 8, pp.15–16, states that for each fixed $0<c<1$ there is an
existential $N_0(c)$ such that every superabundant $N>N_0(c)$ is divisible
by $\operatorname{lcm}(1,\ldots,\lfloor c\log N\rfloor)$.
Proposition 9, p.16, equation (88), states

$$
\frac{d^{(1)}(N)}{\log N}\longrightarrow e^{-\gamma}
\qquad(N\to\infty\text{ through superabundant integers}).
$$

This gives the first cutoff's asymptotic location. That source statement
supplies no explicit $N_0(c)$ certifying one independently fixed critical
integer, and asserts no unbounded sequence of Robin global maximizers.
A finite-source application would need its own effective input.

The approximately 91.85% reported on pp.2–3 is the limiting contribution
of the hook-shaped partition family relative to $e^\gamma$.
Theorem 7, pp.13–14, gives the fixed-$r$ hook limits. These are not a
certified fraction of $\sigma(N)/N$ at a particular integer or a uniform
error estimate when $r$ grows with $N$. The higher-cutoff table retains
its conjectural and finite-list conditions.

The remaining [Robin comparison](nicolas2025comparison.md) still requires
the complete joint signed bound at the same conditional extremal source.
The cutoff definition and its limiting location supply no such bound
for the original zero head and price cost.
