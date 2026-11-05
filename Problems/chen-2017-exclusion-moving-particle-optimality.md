---
slug: chen-2017-exclusion-moving-particle-optimality
bibkey: chen2017movingparticle
doi: 10.1214/17-ECP82
url: https://arxiv.org/abs/1606.01577v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.result
---

# Effective resistance is the optimal finite-graph moving particle constant

## Problem

J. P. Chen, *The moving particle lemma for the exclusion process on a weighted graph*, Electron. Commun. Probab. 22 (2017), paper 47, arXiv:1606.01577v4, §1, `OctopusMoving_v3.tex`, lines 177–179, states:

> However, it is unclear in general when \eqref{Reffinf} becomes an equality.

> That being said, we conjecture that Theorem \ref{thm:dirichletex} is optimal on any finite weighted graph, and more generally, on resistance spaces \cite{KigamiRF}, in light of the connection between the moving particle lemma and the spectral gap of an interacting particle system \cite{Morris, Jara, Quastel}.

These are verbatim TeX excerpts; the labels refer to equation (1.9) and Theorem 1. The definitions and source locators are also recorded in [the literature note](../Library/StatisticalMechanics/chen2017movingparticle.md).

For a finite vertex set $V$, let $c:V\times V\to\mathbb R$ be nonnegative and symmetric, with zero weights representing absent edges. A configuration is $\zeta\in\{0,1\}^V$, $\zeta^{xy}$ exchanges its occupations at $x,y$, and $\nabla_{xy}f(\zeta)=f(\zeta^{xy})-f(\zeta)$. Write $\nu_\alpha$ for the product Bernoulli measure of constant density $\alpha$, and put

$\mathcal E^{\rm el}(h)=\tfrac12\sum_{u\in V}\sum_{w\in V}c_{uw}(h(u)-h(w))^2$,

$\mathcal E^{\rm EX}_{\nu_\alpha}(f)=\tfrac14\sum_{u\in V}\sum_{w\in V}c_{uw}\nu_\alpha[(\nabla_{uw}f)^2]$,

$C(x,y)=\inf\{\mathcal E^{\rm el}(h):h:V\to\mathbb R,\ h(x)=1,\ h(y)=0\}$.

The factors remove ordered-pair double counting and retain the source's additional Dirichlet-energy factor $\tfrac12$ for exclusion. For positive $C(x,y)$, the source's effective resistance is $R_{\rm eff}(x,y)=1/C(x,y)$.

Issue [#24189](https://github.com/the-omega-institute/trureturing/issues/24189) fixes the finite-graph reading: for every such $V,c$, every distinct $x,y\in V$, every $0<\alpha<1$ and every real $k$, if

$\tfrac12\nu_\alpha[(\nabla_{xy}f)^2]\le k\mathcal E^{\rm EX}_{\nu_\alpha}(f)$ for every $f:\{0,1\}^V\to\mathbb R$,

then $1\le kC(x,y)$. This is the proposition `claim` proved by `result`.

## Motivation

Chen's Theorem 1 bounds the exclusion exchange cost by effective resistance times the exclusion Dirichlet energy. The source applies this comparison to graphs without translational invariance and to local ergodicity on Sierpinski gasket graphs (§1.2). Optimality asks whether this electrical comparison already gives the least possible constant, even though the observables range over the entire particle-configuration space.

## Gap

The bounded literature check in issue #24189 reports:

- the conjecture remains in arXiv:1606.01577v4; the quoted source text confirms this;
- the orchestrator (Claude Code, Opus) read Chen's arXiv:1702.03376 and arXiv:1705.10290, Alon–Kozma's arXiv:1811.10537 and Chen–Hinz–Teplyaev's arXiv:1904.08789, finding no settlement of this sharpness question;
- additional citation searches and keyword searches reported no settlement within their searched scope;
- repository and preregistration searches reported no pre-existing record of this problem.

`not-found-in-searched-scope`. The cited follow-up readings and search results are attributed reports, not an independent literature verification.

## Route

Throughout, $V$ is finite and has decidable equality, and potentials and observables are real-valued. The named auxiliary lemmas are private declarations of the canonical module.

1. **Linear observables and moments.** Define $F_h(\zeta)=\sum_{z\in V}h(z)\zeta(z)$. For every potential $h$, configuration $\zeta$ and distinct vertices $u,w$, `linear_gradient` gives $\nabla_{uw}F_h(\zeta)=(h(u)-h(w))(\zeta(w)-\zeta(u))$. For every real $\alpha$ and distinct $u,w$, `bernoulli_second_moment` gives $\nu_\alpha[(\zeta(w)-\zeta(u))^2]=2\alpha(1-\alpha)$, where expectation outside the probability interval denotes the same finite weighted sum. For every real $\alpha$, every $h$ and all $u,w$, including $u=w$, `linear_gradient_moment` consequently gives $\nu_\alpha[(\nabla_{uw}F_h)^2]=2\alpha(1-\alpha)(h(u)-h(w))^2$.
2. **Exact energy transfer.** For every real weight function $c$, every real $\alpha$ and every $h$, `linear_energy` gives $\mathcal E^{\rm EX}_{\nu_\alpha}(F_h)=\alpha(1-\alpha)\mathcal E^{\rm el}(h)$. For every real $\alpha$, every $h,x,y$ with $h(x)=1$ and $h(y)=0$, `boundary_energy` gives $\tfrac12\nu_\alpha[(\nabla_{xy}F_h)^2]=\alpha(1-\alpha)$.
3. **A legitimate infimum.** For arbitrary real weights $c$ and distinct $x,y$, `feasible_nonempty` supplies a unit-voltage potential, namely the indicator of $x$. For nonnegative symmetric $c$ and every $h$, `electric_energy_nonneg` proves $\mathcal E^{\rm el}(h)\ge0$, so the feasible energies are bounded below. For nonnegative symmetric $c$, distinct $x,y$ and real $k$ satisfying $1\le k\mathcal E^{\rm el}(h)$ for every unit-voltage potential $h$, `infimum_bound` proves $1\le kC(x,y)$. Its proof tests a feasible potential to obtain $k>0$, and applies `le_csInf` to the lower bound $1/k$ for all feasible energies.
4. **Cancellation.** For nonnegative symmetric $c$, distinct $x,y$, $0<\alpha<1$ and a real $k$ satisfying the moving particle inequality for every observable, `result` tests that inequality on each unit-voltage $F_h$. The identities in step 2 and $\alpha(1-\alpha)>0$ give $1\le k\mathcal E^{\rm el}(h)$ for every such $h$, which is precisely the hypothesis needed by `infimum_bound`.

## Falsifier

A mismatch in normalization, probability law or admissible observables would prevent the result from answering the conjecture. The module uses:

- `Fin 2` occupations, actual coordinate exchange, and the finite sum against the product Bernoulli mass;
- symmetric ordered-pair weights, with $\tfrac12$ for electrical energy and $\tfrac14$ for exclusion energy; diagonal weights contribute zero;
- the real `sInf` of unit-voltage energies, with feasibility for distinct vertices and the nonnegative energy bound established by the lemmas above;
- all real observables on configurations, distinct endpoints, and strictly interior densities.

The source's display (1.8), at TeX line 170, writes $f:V\to\mathbb R$ inside its optimization problem; its exchange functional acts on $f:\{0,1\}^V\to\mathbb R$, as specified in Theorem 1 and the energy definition. The formal claim uses the latter domain. The quotient is meaningful only when its swap-gradient denominator is nonzero; `claim` avoids division by that denominator. It also allows disconnected conductance networks and makes no assertion for $x=y$ or $\alpha\in\{0,1\}$.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.lean.json`.

Declaration statements:

- `result`: `sha256:aabd457d9e5efdf99405df23c7b9d0b1a3ab1f962bdf9014edac6930c649c8e9`;
- `claim`: `sha256:77420d77c4ea00cff378852e8c8689b7538ca6ca2c867acbd321ae1b731be449`.

## Triage

Tier 1 conjecture stated in a 2016 preprint and retained in the 2017 journal version, preregistered in issue #24189 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every finite vertex type with decidable equality, every nonnegative symmetric real conductance function, every pair of distinct vertices $x,y$, every $0<\alpha<1$ and every real $k$, an inequality $\tfrac12\nu_\alpha[(\nabla_{xy}f)^2]\le k\mathcal E^{\rm EX}_{\nu_\alpha}(f)$ for all real configuration observables implies $1\le kC(x,y)$.

**Computed, not formalized**: none.

**Argued, not formalized.**

- *Sharpness and an attaining observable.* Fix a finite network with nonnegative symmetric conductances, distinct $x,y$, $C(x,y)>0$ and $0<\alpha<1$. Clipping a unit-voltage potential to $[0,1]$ preserves its boundary values and cannot increase any squared difference. The clipped feasible set is nonempty and compact, and its energy is continuous, so there is a minimizing potential $h_*$ with energy $C(x,y)$. The identities `linear_energy` and `boundary_energy`, applied to this finite network, real $\alpha$ and potential with $h_*(x)=1$, $h_*(y)=0$, give a positive exchange cost $\alpha(1-\alpha)$ and exclusion energy $\alpha(1-\alpha)C(x,y)$. Their ratio is $1/C(x,y)$. Chen's published Theorem 1 supplies the matching upper bound when the positive-conductance graph is connected. If $x,y$ lie in one positive-conductance component of a larger network, condition on the occupations outside that component, apply the connected theorem, and average; the other components contribute nonnegative exclusion energy. They can be assigned constant electrical potentials, so the full network has the same $C(x,y)$ as the component. The zero-conductance argument below excludes separate components when $C(x,y)>0$. Thus $R_{\rm eff}(x,y)$ is the least admissible constant and equality in (1.9) holds at every such density. The decisive structure is the exact transfer on linear observables; characterizing equality in the octopus inequality is unnecessary for this sharpness argument.
- *Degenerate networks and densities.* Under the hypotheses of `result`, if $C(x,y)=0$, any admissible finite real $k$ would give $1\le0$, so no such $k$ exists. In particular, if no positive-conductance path joins $x$ to $y$, the indicator of the positive-conductance component of $x$ is feasible with zero energy; nonnegativity of all feasible energies gives $C(x,y)=0$. At density zero or one the measure is supported on a constant configuration, fixed by every swap, so both sides of the moving particle inequality vanish for every $f$ and every real $k$. For $x=y$ the exchange cost likewise vanishes. These cases cannot support the same nontrivial lower bound.
- *A neighbouring ensemble.* For the uniform law on configurations with exactly $m$ occupied vertices, where $n=|V|\ge2$ and $1\le m\le n-1$, counting configurations gives $\mathbb P(\zeta(u)=1,\zeta(w)=0)=\binom{n-2}{m-1}/\binom nm=m(n-m)/(n(n-1))$ for distinct $u,w$. Thus the expected squared occupation difference is twice this positive number. The same linear-observable calculation replaces $\alpha(1-\alpha)$ by $m(n-m)/(n(n-1))$ in both energies. For nonnegative symmetric conductances and distinct endpoints, cancellation and the nonempty, bounded-below unit-voltage infimum therefore give the same necessary bound $1\le kC(x,y)$ for any inequality valid for every observable in that particle-number sector. This sector statement is an unformalized consequence of the counting argument, not a clause of `result`.
- *Effect on the source and remaining questions.* Equality in the finite-graph optimization (1.9), under the positive-conductance and interior-density conditions above, resolves the finite-graph optimality question. The Sierpinski gasket comparison and local-ergodicity discussion in §1.2 use the upper bound of Theorem 1; they require no added sharpness assumption. Pairwise optimality does not determine the best constant in a coarser resistance estimate used there. Optimality on resistance spaces, a classification of all equality observables, and general equality conditions for the octopus inequality remain open in this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded by the sources and queries reported in #24189 and does not establish exhaustive worldwide novelty or priority. Apart from arXiv:1606.01577v4 itself, the source readings and searches reported there are not independently reproduced: this includes arXiv:1702.03376, 1705.10290, 1811.10537 and 1904.08789, and the search contributor's reported arXiv:2106.03685, 2311.02505, 2602.19059, 2606.09728, 2608.25506, 2609.03746 and 2610.10736, OpenAlex, Semantic Scholar and web-search results. The source quotation is checked against the v4 TeX; a separate comparison with the typeset journal text is not supplied.

Chen's upper bound, the identification of the two graph-sum conventions with the source, and the mathematical arguments under “Argued, not formalized” are not additional compiled conclusions of `result`. In particular, minimizer attainment, quotient equality, the zero-conductance and endpoint consequences, and the fixed-particle-number extension are not separately formalized in this module. Resistance spaces and the remaining equality questions are not settled by the finite-graph result.
