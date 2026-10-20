---
slug: roldan-2026-integral-circulant-energy-p2q3
bibkey: roldan2026integralcirculant
doi: 10.48550/arXiv.2604.09491
url: https://arxiv.org/abs/2604.09491v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/RoldanCirculantEnergyP2Q3.result
---

# Unique integral circulant energy maximum at order $p^2q^3$

## Problem

D. G. Roldán, *Graph Energy Maximisation for Integral Circulant Graphs of Order n = p^2q^3*, arXiv:2604.09491v1, Section 1, Conjecture 1.3 (Universality):

> For every pair of distinct odd primes (p, q), the set D* = {1, p^2, pq, q^2, p^2q^2, pq^3} is the unique maximiser of E(p^2q^3, D) over all nonempty D ⊆ div(p^2q^3) ∖ {p^2q^3}.

The graph has vertices $\mathbb Z_n$ and adjacency condition $\gcd(a-b,n)\in D$. Its energy is the sum of the absolute values of its adjacency eigenvalues, with multiplicity. Source quotations and locators are in [the literature note](../Library/GraphInvariants/roldan2026integralcirculant.md). Preregistration: [#19144](https://github.com/the-omega-institute/trureturing/issues/19144).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Vertices $\mathbb Z_n$, modular difference, gcd adjacency | `adjacency n D`, on `Fin n` | Literal preregistered expression; subtraction is modulo $n$. |
| Energy sums $|\lambda_i|$ with multiplicity | `energy n D`, using the multiset roots of the real characteristic polynomial | The proof identifies all roots through Fourier diagonalization of the real symmetric adjacency. |
| Distinct odd primes $p,q$ | `claim` quantifies $p,q$ with both primality, inequality and oddness hypotheses | No ordering of $p,q$ and no restriction $q\ge5$. |
| $D^*=\{1,p^2,pq,q^2,p^2q^2,pq^3\}$ | `Dstar p q` | Literal six-term finite set. |
| Allowed, nonempty proper-divisor sets | First conjunct of `claim` and the guards on its quantified `D` | The first conjunct proves admissibility of $D^*$; $1\in D^*$ gives nonemptiness. |
| Unique maximizer | Strict energy inequality for every different allowed nonempty `D` | Full proposition, proved by `result : claim`. |

No additional premise restricts the published conjecture. The spectral argument proves the comparison even when the competing divisor set is empty.

## Motivation

The later Jiang–Yang result, arXiv:2608.29523v1, covers $q\ge5$ and explicitly leaves $q=3$ uncovered. A uniform proof for all distinct odd primes closes this exceptional family and Conjecture 1.3 as stated.

## Gap

The source and literature readings in #19144 identify the unproved $q=3$ family. The searched literature includes the later partial result, surveys of integral circulant energy and multiplicative divisor sets, and open-problem catalogs. This is `not-found-in-searched-scope`; completeness is `ASSUMED-UNVERIFIED`.

## Route

Fourier diagonalization gives eigenvalues as Ramanujan sums. Grouping frequencies by their gcd with $n$ gives totient multiplicities. For $n=p^2q^3$, prime-power divisors form a $3\times4$ grid; the excluded divisor $n$ leaves eleven Boolean choices, encoded by masks below $2048$.

Set $u=p-3\ge0$ and $v=q-3\ge0$. Each of the twelve spectral classes has an integer coefficient polynomial. Replacing its coefficients by their absolute values gives an upper bound on its absolute value throughout the nonnegative quadrant. For the mask $1445$ of $D^*$, all coefficients in each class have one sign, so this bound is attained. The finite coefficient certificate gives a positive deficit for every other mask. `model_gap` proves a deficit of at least $96$ for every competing mask and all nonnegative real $u,v$. `result` transports this comparison to the original adjacency energy.

The Fourier and Ramanujan arguments reuse the original declarations in `PolygonalFourierCouplings` and `FiniteRamanujanDivisorIdentity`; no separate general spectral supplier is required. The fixed certificate is in `RoldanCirculantEnergyP2Q3Certificate` and is consumed by the settling module.

## Falsifier

A distinct pair of odd primes and a different nonempty proper-divisor set with energy at least that of $D^*$ would contradict the claim. A different graph convention, an energy omitting multiplicities, allowing the divisor $n$, or allowing the prime $2$ changes the statement and is outside this settlement.

## Evidence

The settling declaration is `D5/S3/Arith/RoldanCirculantEnergyP2Q3.result`. The certificate comparison is `D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.model_gap`. Lean proof evidence and the independent numerical computation are distinct evidence kinds. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The [escape audit #19204](https://github.com/the-omega-institute/trureturing/issues/19204) is unfinished. It covers the two new public theorems and the published owner theorems `transform_unitary`, `circulant_spectral`, and `sum_ramanujanSum_divisors`. No `declared_validated` registration is claimed. Faithful reconstruction, realization, variation, sensitivity and observational dependence evidence for their full statements remains missing.

### Independent experiment

[Experiment directory at commit `931fed54e9a0f090cb4d77b00ef05b78581d8482`](https://github.com/the-omega-institute/trureturing-experiments/tree/931fed54e9a0f090cb4d77b00ef05b78581d8482/docs/reports/roldan-2026-icg-energy-p2q3).

Command: `python3 check.py` from that directory; exit $0$; `check.py` SHA-256 `7e5e620660c968566401ade3a1bfa4994eace8bc27f27e6518cdeb02a275143d`.

Computed scope: all $2047$ nonempty proper-divisor sets for each of $(5,3),(7,3),(11,3),(13,3),(17,3),(3,5),(3,7),(5,7),(7,5),(11,5)$; all $2047$ competing masks for the coefficient certificate; and the direct $675\times675$ adjacency spectrum of $D^*$ at $(5,3)$. All ten finite searches find $D^*$ uniquely maximal. At $(5,3)$ its energy is $4832$ and the runner-up is $4424$; the direct adjacency calculation gives $4832$ to its floating-point tolerance. These finite and numerical readings do not establish the unbounded theorem.

## Triage

Tier 1 external named conjecture, preregistered in #19144. Resolution: Proved. Admission basis: `open-problem-resolution (#19144; Proved)`.

| Target item | Status and evidence kind |
| --- | --- |
| $q=3$ | Proved in Lean by `RoldanCirculantEnergyP2Q3.result`: its hypotheses permit $q=3$, and the assembly requires $v\ge0$. |
| Uniform energy gap | Proved in Lean by `RoldanCirculantEnergyP2Q3Certificate.model_gap`: for every competing mask and $u,v\ge0$, the deficit is at least $96$. Transport to the graph energy is used inside `result`. |
| Generic supplier packaging | Implemented by reusing the existing Fourier and Ramanujan owners and placing the finite coefficient certificate in its own instance module. This is a source/dependency fact, not a new mathematical theorem. |
| Canonical D5/Scribe/freeze integration | Delivered through the canonical source, its Scribe mirrors and writer-produced state records. |
| Reg integration | Open: escape audit #19204; no validated four-slot registration is claimed. |
| Agreement at $(p,q)=(5,3)$ | Computed by the experiment: coefficient evaluation, Ramanujan energy and the direct adjacency spectrum give $4832$. The comparison with the source's Theorem 1.2 is a source reading recorded in #19144, not a separate Lean theorem. |

### What the settlement shows

**Proved in Lean:** `result` gives admissibility and strict unique maximization for all distinct odd primes, including $q=3$. `model_gap` supplies the stronger real-parameter model comparison for every $u,v\ge0$, including either boundary value zero.

**Proved in prose from the coefficient comparison:** write $S$ for the optimum coefficients and $\Delta$ for the coordinatewise deficit. For any competing mask, $E(X)\le U_X$ and $E(X^*)=U_{X^*}$; the certificate gives $\operatorname{coeff}(U_X)\le S-\Delta$. Evaluating with $u,v\ge0$ preserves this inequality, hence the deficit is at least

$$96+136v+56v^2+8v^3+(94+128v+54v^2+8v^3)u+(24+32v+14v^2+2v^3)u^2.$$

Every coefficient is positive. This expression is at least $96$ and increases in either nonnegative variable. The public `model_gap` theorem states the constant lower bound; the full polynomial expression is the explained consequence of the coefficient comparison, not a separate public Lean theorem.

**Mechanism:** sign coherence makes the coefficient majorant exact at $D^*$; every competing mask loses a positive amount in each coefficient. Thus the boundary $v=0$ causes no loss of strictness. The argument covers the entire published conjecture; the earlier $q\ge5$ theorem retains its stated scope, and the exceptional family no longer requires a separate argument.

**Open:** analogous classifications for other exponent pairs, optimal sharp graph-energy deficits, and a completed four-slot escape registration. No statement about those extensions is included in `result`.

## ASSUMED-UNVERIFIED

The literature screen is bounded and does not establish exhaustive worldwide novelty or priority. The inaccessible submitted general-exponent paper named in #19144 is outside the checked source set. Floating-point adjacency eigenvalues are numerical corroboration; the Lean theorem does not rely on them. The escape audit remains unfinished as specified in #19204.
