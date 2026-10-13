---
slug: fuks-fates-2026-diploid-10-245-density
bibkey: fuksfates2026diploid
doi: 10.1140/epjs/s11734-026-02447-z
url: https://arxiv.org/abs/2607.01917v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.result
---

# The diploid cellular automaton 10-245 has exact density 1/4 + λ/2

## Problem

H. Fukś and N. Fatès, *Analysis of the asymptotic density of endogamous diploid cellular automata*, arXiv:2607.01917v1 (EPJ ST 2026), study probabilistic cellular automata on ℤ in which every cell independently applies elementary rule f with probability 1 − λ and rule g with probability λ: w(1|x₁x₂x₃) = (1−λ) f(x₁,x₂,x₃) + λ g(x₁,x₂,x₃) (Eq. (2)). Starting from the symmetric Bernoulli measure, d_t = Pr(s_i(t) = 1) is the density and d∞ = lim d_t (§2). For rule 10-245, third-order local structure approximation predicts d∞ = 1/4 + λ/2 (§3.2), while mean-field and second-order approximation give a nonlinear curve. §5 asks: "for rule 10-245, the expression for the asymptotic density, d = 1/4 + λ/2, appears to be exact. Could this be formally demonstrated?" The verbatim statements are in [the literature note](../Library/StatisticalMechanics/fuksfates2026diploid.md).

Issue [#16027](https://github.com/the-omega-institute/trureturing/issues/16027) fixes the reading: for every λ ∈ [0, 1], with the lattice process encoded by its cylinder probabilities (independent simultaneous updates of each interval from its n + 2 parents, fair Bernoulli start), d_t → 1/4 + λ/2. The settlement proves the stronger d_t = 1/4 + λ/2 for every t ≥ 1.

## Motivation

The paper sorts the 168 endogamous diploid rules into six classes by the shape of d∞(λ) and tests how far local structure theory predicts them. Rule 10-245 is its example of the linear class. An exact density there decides whether the agreement with third-order local structure theory is a coincidence of the numerics or a property of the rule.

## Gap

Issue #16027 records the literature check before any Lean:
- arXiv lists only v1, which states the question;
- the citing works found do not treat rule 10-245;
- the source's exactly solvable family (§4.1, [Fuk18]) has absorbing entries and does not contain this rule for 0 < λ < 1;
- Zenodo, Crossref and web searches return no settlement;
- the repository had no probabilistic cellular automaton result.

`not-found-in-searched-scope`.

## Route

Let α = 1 − 2λ and A_i = (1 − x_{i−1}) x_{i+1}.
1. **The kernel.** Rule 10 outputs 1 exactly on the neighbourhoods 001 and 011, and rule 245 is its complement, so w(1 | x_{i−1} x_i x_{i+1}) = λ + α A_i.
2. **Two moments.** Let d_t be the density and q_t the probability of a 0 followed by a 1 at distance two.
   - Shift invariance gives d_{t+1} = λ + α q_t.
   - Conditional independence of the fresh updates gives q_{t+1} = E[(1 − w_0) w_2].
   - Since x(1 − x) = 0 for a spin, A_0 A_2 = (1 − x_{−1}) x_1 (1 − x_1) x_3 = 0 pointwise. Hence q_{t+1} = λ(1 − λ) + α² q_t.
3. **The fixed point.** λ(1 − λ) = (1 − α²)/4, so q_{t+1} − 1/4 = α² (q_t − 1/4). The Bernoulli start has q_0 = 1/4, so q_t = 1/4 for every t and d_{t+1} = 1/4 + λ/2.

## Falsifier

The settlement would fail if the cylinder hierarchy were not the source's process: if updates were not independent given the parents, if a finite ring replaced ℤ, or if the start were not fair Bernoulli. The Lean definitions fix all three, and `CylinderLaw` (nonnegativity, unit mass, consistency at both ends) is part of the proved statement. The closure is special to 10-245. For the paper's rule 36-219, which has the same mean-field equation, the exact density departs from 1/4 + λ/2 at t = 2, e.g. 1389/5488 ≠ 9/28 at λ = 1/7 (#16027).

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.lean` (346 lines).
- Public declarations: the definitions `rule10`, `rule245`, `p`, `w`, `evolve`, `P`, `d` and `CylinderLaw`; `claim` and `result`.
- It uses Mathlib only: `Bool.toNat`, `Fin.consEquiv`, `Fin.snocEquiv`, `Equiv.sum_comp`, `Fintype.sum_prod_type`, `Fintype.sum_bool` and `tendsto_atTop_of_eventually_const`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration `Reg/D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.lean` (template `DependentFamily.realize`, readout the parameter λ) is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.lean.json`, statement `sha256:e1a397273d8d689bbaa3003d47ba7b5b94b6f2f6162ef3af323bebb066b88e1b`.

Declaration statements:
- `result`: `sha256:8b2d23d003bb6787976d83ef0de532eb3bdf769ec5069ec5ca259ede605c9768`;
- `claim`: `sha256:b80994b578869f064d14db232894fb6b0023647e614d43bbd7e78b12f7e7077d`.

## Triage

Tier 1 question of a 2026 paper, preregistered in issue #16027 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every other declaration is a definition used by `claim` or a private helper on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every λ ∈ [0, 1], d_t = 1/4 + λ/2 for every t ≥ 1, and d_t → 1/4 + λ/2. This holds at both endpoints λ = 0 and λ = 1, where the rule is deterministic.

**Established inside the proof.**
- The cylinder hierarchy is a family of probability laws consistent at both ends.
- d_{t+1} = λ + α q_t and q_{t+1} = λ(1 − λ) + α² q_t.
- q_t = 1/4 for every t.

**Argued, not formalized.**
- *The mechanism.* The density sees the configuration only through q, the 0·1 correlation at distance two, and the update of q closes on itself because the two neighbourhood events A_0 and A_2 exclude each other pointwise. This is also why third-order local structure theory, which keeps three-block probabilities, can reproduce the density exactly. Mean-field replaces q_t by (1 − d_t) d_t, which turns d_{t+1} = λ + α q_t into the source's nonlinear Eq. (6), d_{t+1} = λ + α d_t (1 − d_t); the source reports that second order gives the same equation.
- *Other starts.* For any shift-invariant initial law the same recursion gives d_{t+1} = 1/4 + λ/2 + α^{2t+1}(q_0 − 1/4) (checked exactly for several λ and q_0). For 0 < λ < 1 the density converges geometrically to 1/4 + λ/2 from every such start. At λ = 0 it is d_{t+1} = 1/4 + (q_0 − 1/4), and at λ = 1 it is d_{t+1} = 3/4 − (q_0 − 1/4); both depend on the start.
- *What constancy does not say.* Only d and q are pinned; constant density does not by itself make the law Bernoulli or stationary. At λ = 1/2 every update probability is 1/2 and the fair Bernoulli law persists; for other λ the proof says nothing about the law beyond d and q.

**Open.**
- The source's companion question, whether third-order local structure theory is exact for rule 39-219, is not addressed.
- The full stationary law of 10-245 is not identified.

**Effect on the paper.** The §5 question has a positive answer. Rule 10-245's membership in the linear class is a theorem, with d_t constant from the first step.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
