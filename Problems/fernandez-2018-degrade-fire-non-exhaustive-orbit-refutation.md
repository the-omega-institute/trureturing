---
slug: fernandez-2018-degrade-fire-non-exhaustive-orbit-refutation
bibkey: fernandez2018revisiting
doi: 10.1140/epjst/e2018-800068-8
url: https://arxiv.org/abs/1809.03228v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.result
---

# A non-exhaustive periodic orbit in Fernandez's three-cell degrade-and-fire chain

## Problem

Bastien Fernandez, *Revisiting asymptotic periodicity in networks of degrade-and-fire oscillators* (Eur. Phys. J. Spec. Top. 227, 1267–1279, 2018; arXiv:1809.03228v1; DOI 10.1140/epjst/e2018-800068-8), states in the Concluding Remarks, `DynamicsDFNetworksRevised.tex`, line 373:

> We believe that similar impossibility prevails for any other periodic trajectory with non-exhaustive firing in this graph.

The graph is the right transition graph in Figure 1, for the Section 4 system with $N=3$, $\epsilon>1/2$ and coupling matrix

$$
W=\begin{pmatrix}1-\epsilon&0&\epsilon\\ \epsilon&1-\epsilon&0\\ 0&\epsilon&1-\epsilon\end{pmatrix}.
$$

The source assumes $0<\eta<1$, $\epsilon<1-\eta$, initially $(Wx)_j>\eta$ for every cell, and restricts to trajectories with distinct coordinates and no simultaneous firings (Section 4, lines 239–255). Exhaustiveness means that every three consecutive firing labels form a permutation of the three cells (line 68). The quoted belief extends the source's exclusion of a particular six-firing itinerary to every non-exhaustive periodic trajectory in this graph.

Issue [#25922](https://github.com/the-omega-institute/trureturing/issues/25922) fixes the formal reading. Write $\theta$ for the source's $\eta$. For every real $\theta,\epsilon$ with $0<\theta<1$ and $1/2<\epsilon<1-\theta$, and every state sequence $s:\mathbb N\to\mathbb R^3$, label sequence $\mathrm{lab}:\mathbb N\to\mathrm{Fin}\,3$ and waiting-time sequence $\tau:\mathbb N\to\mathbb R$, `claim` says that initial repressors strictly above $\theta$, `IsRun ε θ s lab τ`, and `IsPeriodic s` imply `IsExhaustive lab`. Lean labels $0,1,2$ correspond to the source's $1,2,3$. This assertion is refuted.

## Motivation

Exhaustive firing is an explicit hypothesis of the source's periodic-orbit and asymptotic-periodicity results. Excluding other periodic itineraries would help classify the recurrent behavior of the strongly coupled three-cell chain. The refutation supplies a periodic itinerary outside that restriction while retaining distinct coordinates and unique firings.

## Gap

The bounded literature check in #25922 records searches of OpenAlex and Crossref citation records, readings of two citing works, and checks of the related preprints by Blumenthal and Fernandez (2014, arXiv:1411.1595; 2015, arXiv:1502.06088) and Fernandez and Tanzi (2024, arXiv:2405.07752). It also records repository issue searches for degrade-and-fire, Fernandez and 1809.03228 together with checks of `Problems/` and `Library/`. It reports no settlement in that scope. The issue attributes the citing-work and related-paper readings to the search seat; they are not independent readings supplied by this dossier.

`not-found-in-searched-scope`.

## Route

1. **The witness.** Set $\theta=3/20$ and $\epsilon=4/5$. The private definitions `orbit`, `firing` and `duration` repeat the nine entries of `states`, `labels` and `times` modulo $9$. The initial state is $(11/32,0,1)$; the source-indexed firing word is $(2,2,2,1,1,1,3,3,3)$, and the waits repeat $(5/32,1/4,1/4)$ three times.
2. **Every segment.** For these fixed parameters and every $i\in\mathrm{Fin}\,9$, `block_verified` establishes all seven run conditions: the assigned wait is positive; every repressor is strictly above $3/20$ for every $t$ with $0\le t<\mathrm{times}(i)$; the selected cell is at or below $3/20$ at the endpoint; every other cell $j\ne\mathrm{labels}(i)$ is strictly above it there; the degrading coordinates are pairwise distinct for every $0\le t\le\mathrm{times}(i)$; the succeeding state has distinct coordinates; and resetting the selected endpoint coordinate to $1$ gives precisely that succeeding state, with succession in $\mathrm{Fin}\,9$. Here `cut t x` has coordinate $\max(x_j-t,0)$, as in the source's saturation-at-zero rule.
3. **The infinite run and its period.** `run_verified` establishes `IsRun (4/5) (3/20) orbit firing duration` by reducing arbitrary natural indices modulo $9$. `initial_verified` gives initial repressors strictly above $3/20$ for every cell. `periodic_verified` establishes `IsPeriodic orbit` with the positive natural period $9$: $s_{k+9}=s_k$ for every natural $k$.
4. **Contradiction.** `non_exhaustive_verified` establishes that `firing` is not exhaustive: its first three Lean labels are all $1$, so that window is not injective. The strict parameter inequalities $0<3/20<1$ and $1/2<4/5<1-3/20$ allow `result` to apply the proposed universal implication to this run and obtain a contradiction.

## Falsifier

The refutation must respect the source's flow, matrix orientation, parameter range and exclusions. The definition `coupling ε` is the circulant with first column $(1-\epsilon,\epsilon,0)$, hence exactly the displayed matrix. The reset changes only the selected coordinate to $1$. `IsRun` requires unique endpoint firing and distinct coordinates throughout each closed degrading segment and immediately after resetting.

Two formal boundaries matter. `IsRun` has no coordinate-range premise: it is defined on real vectors. The explicit witness nevertheless belongs to the source's cube $[0,1]^3$: every listed state has coordinates in $[0,1]$, subtracting nonnegative time and clipping at zero preserves that range, and resetting to $1$ also preserves it. This range argument is not a separate Lean theorem in the module. `IsPeriodic` requires only a positive natural period for the post-firing states; periodicity of the labels and waits is supplied here by their explicit modulo-$9$ definitions. The corresponding continuous-time interpretation is discussed below.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:a2eeffbcdf5653376a75b8a3a9e4c18962a028bce6da919adc1220d3339eeb80`;
- `claim`: `sha256:3cebdab8f6de1eb7b0d28b3bead6b494edde513ad8c0cf9ae9fee4c5cce70f81`.

## Triage

Tier 1 stated belief of a 2018 paper, preregistered in issue #25922 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal assertion `claim` is false: it is not true that, for every $0<\theta<1$, every $1/2<\epsilon<1-\theta$ and every $s,\mathrm{lab},\tau$, initial repressors strictly above $\theta$, `IsRun ε θ s lab τ` and a positive natural period for $s$ imply that every three consecutive firing labels form a bijection of the three cells.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism.* Saturation allows another cell to remain at zero while the reset cell fires repeatedly. At the fixed parameters $\theta=3/20$, $\epsilon=4/5$, `block_verified` for $i=1,2\in\mathrm{Fin}\,9$ supplies all segment and reset conditions listed in Route. After the first reset the state is $(3/16,1,27/32)$; on the interval $3/16\le t\le1/4$, its first coordinate is zero, so the second repressor equals $(1-t)/5$ and reaches $3/20$ at $t=1/4$. From the next state $(0,1,19/32)$ the same expression permits another reset of cell $2$ after $1/4$. Thus visiting a self-loop twice changes the return condition from the six-firing itinerary considered in the source. Excluding one prescribed itinerary cannot exclude all possible numbers of consecutive repeated firings.
- *Continuous time.* The witness's states, labels and positive waits all repeat after nine firings. Concatenating the same nine degrading segments and resets therefore repeats the entire motion after the sum of those waits, $63/32$. Since each wait is at least $5/32$, the construction has no accumulation of firings in finite time. This interpretation and the coordinate-range argument are not additional conclusions in the type of `result`.
- *Nearby questions.* Section 2 defines non-degeneracy by requiring that “every expression level that vanishes at some time is reset at the next firing” (line 79). The witness violates this stronger condition when its first coordinate reaches zero during a segment ending in a reset of cell $2$; Section 4.1 does not impose that condition. Whether imposing non-degeneracy, or forbidding zero coordinates altogether, restores the proposed exclusion is open here. A single orbit and four further tested initial states do not determine attraction, basin measure or the prevalence of non-exhaustive recurrence. In particular, they do not settle the source's separate belief that such firings are “rare, if not exceptional in the asymptotic dynamics” (line 373).
- *Effect on the paper.* The universal exclusion in the Concluding Remarks cannot justify discarding all non-exhaustive periodic itineraries for $\epsilon>1/2$. The source's six-firing calculation concerns a different itinerary and is not itself contradicted by this witness; its nonexistence conclusion is not independently certified here. The uniqueness result for non-degenerate minimal orbits under primitive coupling in Section 2 and the convergence result under irreducible doubly stochastic coupling and a compatible exhaustive firing word in Section 3 explicitly impose their own hypotheses and do not invoke this belief. The counterexample lies outside their scope with exhaustive firing. The Section 4.2 analysis for $\epsilon\le1/2$ concerns a disjoint parameter range.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches recorded in #25922 and establishes neither exhaustive novelty nor priority. The OpenAlex/Crossref citation listings, the readings of the two citing works and three related preprints, and the preregistration's repository-search results were not independently reproduced. No independent check that arXiv v1 is the only version is claimed.

The arguments labelled above are not additional Lean theorems. In particular, the coordinate-range and continuous-time bridges are arguments from the explicit witness. The one-parameter family for every initial first coordinate in $(1/4,7/16)$, reported by the search seat in #25922, is not established here. The source's six-firing nonexistence calculation, possible restoration under non-degeneracy or a no-saturation restriction, attraction, rarity and other parameter regimes are not settled by this module.
