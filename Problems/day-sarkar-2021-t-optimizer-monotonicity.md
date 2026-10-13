---
slug: day-sarkar-2021-t-optimizer-monotonicity
bibkey: daysarkar2021extremaldensities
doi: 10.1137/19M1296525
url: https://arxiv.org/abs/1910.13465
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.result
---

# The optimal T-parameter is not monotone in edge density

## Problem

A. N. Day and A. Sarkar, *On a Conjecture of Nagy on Extremal Densities*, SIAM Journal on Discrete Mathematics 35 (2021), 294–306, DOI 10.1137/19M1296525, arXiv:1910.13465v1, Section 5, p. 14, state verbatim:

> **Conjecture 2.** For each graph $G_l$, we have that $q(G_l,\beta)$ is an increasing function of $\beta$.

The source takes a maximiser of $q\mapsto t(G_l,T_n^e(q))$ on $[0,1]$. The public `claim` uses the weakest reading: for every finite labelled simple graph, there exists a nondecreasing selection of maximisers at all densities in $[0,1]$. Its negation also excludes a strictly increasing selection.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every labelled finite graph $G_l$ | `v : Nat`, `G : SimpleGraph (Fin v)` in `claim` | All finite orders, including zero; labels introduce no restriction. |
| Class sizes $\sqrt\beta qn$, $(1-\sqrt{1-\beta(1-q^2)})n$, $(\sqrt{1-\beta(1-q^2)}-\sqrt\beta q)n$ | `yW`, `rW`, `bW`, `vertexClass` | Yellow and red sizes use natural floors; blue is the remainder. Floors do not change the proved limit. |
| Yellow and red cliques; red joined to both other classes; blue independent; no yellow–blue edges | `classAllowed`, `tGraph` | Adjacency requires unequal endpoints. |
| Adjacency-preserving functions, not necessarily injective | `homCount` | Literal cardinality of the source homomorphisms. |
| Homomorphism density as a limit | `tDens` | Literal `limUnder` along natural graph orders; `tDens_eq_weightingSum` proves the limit formula. |
| Parameter attaining the supremum on $[0,1]$ | Membership and `IsMaxOn` conjuncts in `claim` | Every chosen parameter is a maximiser. |
| Increasing with density | `MonotoneOn` in `claim` | Nondecreasing selection is the weaker interpretation. The witness densities lie strictly inside $(0,1)$. |
| Fractional independence weightings | `independentWeight`, `admissible`, `weightingSum` | Classes red, yellow and blue have indices $0,1,2$, representing weights $0,1/2,1$. |

## Motivation

A monotone selection would constrain how extremal threshold graphons interpolate with edge density. The source's STK type proposal assumes Conjecture 2. A failure for a graph with a pendant star therefore affects that proposed classification independently of the extremal-value questions.

## Gap

Let $H_3$ have vertex set $\{0,\ldots,6\}$ and edges $01,12,20,03,34,35,36$. At $\beta_1=10^{-6}$ and $\beta_2=10^{-4}$ each maximiser is unique, and every maximiser satisfies

$$
q(H_3,\beta_1)>\frac{7743}{10000}>\frac{7719}{10000}>q(H_3,\beta_2).
$$

Thus no choice of maximisers can satisfy the monotonicity clause. The source definitions remain literal; the finite floors and the weak selection interpretation are explicit conventions.

## Route

The supporting module `ThreeClassHomomorphismLimit` proves the floor-sized three-class homomorphism limit equals the finite weighting sum. Its private `bad_count_bound` bounds the maps with an edge collision by $v^2 n^{v-1}$; nonadjacent vertices may share images. The error divided by $n^v$ tends to zero, including the separate $v=0$ case.

The settling module uses that limit for $H_3$, evaluates the colouring sum, and puts $s=\sqrt\beta$, $z=r+y$, $x=z/s$. The rational coordinate is used only for $0<s\le1/100$, and each rational identity or derivative requires $1-sx\ne0$. These two restrictions are part of the proved route.

The normalized density derivative factors as

$$
\frac{d}{dx}(D_3/s^5)=\frac{(sx^2+s-2x)Q_s(x)}{16(sx-1)^4}.
$$

The octic $Q_s$ is strictly increasing on $[1/2,1]$. For admissible coordinates at most $1/2$, the normalized density is less than $83/1000$; its value at $3/4$ exceeds $9/100$ at both chosen densities. Sign evaluations isolate the respective roots in $(77451/100000,77452/100000)$ and $(77384/100000,77385/100000)$. Continuity and compactness supply maxima; strict monotonicity of the octic and injectivity of the coordinate give uniqueness. The increasing coordinate transfers the two intervals to reversed bounds on $q$.

## Falsifier

The private `unique_max_one`, `unique_max_two` and `maximisers_reversed` establish the two unique maxima and their reversed order. The public `D5.S3.Combinatorics.ExtremalDensity.NagyOptimizerMonotonicity.result` proves the literal negation of `claim` using this seven-vertex graph. These are exact bounds and uniqueness statements, not numerical approximations to the maximisers.

## Evidence

The Lean sources are `D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.lean` and `D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.lean`, with corresponding Blueprint Scribes. The supporting module has admission basis `escape-witness` with `bad_count_bound`; the settling module has `open-problem-resolution (#15853; Refuted)`. Both have `utility: none`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

### Experiment

[The numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/4ab6233703b64d1b620f7f446758641461eb157d/docs/reports/day-sarkar-2021-t-optimizer-monotonicity) is pinned to commit `4ab6233703b64d1b620f7f446758641461eb157d`. The script is `check.py`, SHA-256 `c9befdf9b9baf9f81551dd7b766e816f00e225bbb59098ae101aed01b0a74677`. Command: `python3 /tmp/op-ds-check.py`, executing exactly that pinned script; exit 0, `bad=0`.

The colouring sum agrees with the closed form within $10^{-30}$ for $k\in\{2,3,4,5\}$ at $(\beta,q)\in\{(0.01,0.6),(0.0001,0.77),(0.3,0.2)\}$. The derivative identity is checked symbolically for $H_3$, and the octic endpoint signs are checked in exact rationals at $s=1/1000$ and $s=1/100$. The induced intervals are approximately $(0.7743097777959508,0.7743197855451004)$ and $(0.7718184985411105,0.771828576325394)$.

The grid/Newton candidates use a 4000-point grid, 40-digit arithmetic, $k\in\{2,3,4,5\}$ and $\beta\in\{10^{-8},10^{-6},10^{-4},10^{-3},10^{-2}\}$. They increase for $k=2$ and decrease for $k=3,4,5$ over those five sampled densities. For $k=3$ the values are $0.7745686723$, $0.7743169790$, $0.7718275585$, $0.7660503086$, $0.7497563318$. Sampling supplies no monotonicity assertion between the sample points or uniform assertion over $k$; the exact $H_3$ settlement is supplied by Lean.

### Escape audit

The audit is unfinished under [#15978](https://github.com/the-omega-institute/trureturing/issues/15978) for `ThreeClassHomomorphismLimit.weights_valid`, `ThreeClassHomomorphismLimit.tDens_eq_weightingSum` and `NagyOptimizerMonotonicity.result`. Both modules use `utility: none`, so the settling result has no refutation exemption. The targeted production DTR rule reads `DTR-Unregistered` (Observe) for all three public theorems listed above; no four-slot registration is delivered.

Finite pointwise equality/order and guarded equality readouts do not retain both unrestricted real coordinates and the unbounded graph domain. The enrolled `DependentFamily.realize` can represent dependent families, but the supporting registrations lack variation, sensitivity, observational-dependence and exact source-reconstruction evidence. For `result`, a faithful readout must additionally retain the graph-dependent quantifiers over maximiser selections and the negated monotonicity clause; no such source-selection/realization bridge and variation/sensitivity evidence is supplied. No failed Reg source is delivered.

## Triage

### What the settlement shows

1. **Kernel-checked — Conjecture 2 is refuted.** `NagyOptimizerMonotonicity.result` proves that no monotone selection exists for all finite graphs. Its private uniqueness and reversed-bound lemmas establish the exact $H_3$ witness at $10^{-6}$ and $10^{-4}$. This does not classify all graphs or all densities.

2. **Proved in prose — downward drift for each fixed $k\ge3$.** Let $H_k$ be a triangle with one vertex joined to the centre of a $k$-leaf star, and $z=r+y$. Splitting on the star centre gives

   $$
   D_k=rz^3+3br^3+yz^{k+3}+2byr^2z^k+br^{k+1}\beta.
   $$

   A red centre contributes $r(z^3+3br^2)$: all leaves may use any class, whose weights sum to one. A yellow centre contributes $yz^k(z^3+2br^2)$: its leaves may be red or yellow, and a blue triangle vertex can occupy either of the other two positions. A blue centre forces the joined triangle vertex and all leaves to be red, contributing $br^{k+1}(z^2+2br)$; the source weights satisfy $z^2+2br=\beta$.

   Write $A=1-q^2$ and $s=\sqrt\beta$. Then $r=s^2A/2+O(s^4)$, $y=sq$, $b=1-sq-r$. For each fixed $k\ge3$, uniformly on $q\in[0,1]$,

   $$
   D_k/s^5=F_0(q)+sF_1(q)+O(s^2),\qquad
   F_0(q)=\frac{q^3(1-q^2)}2,\quad
   F_1(q)=\frac{3(1-q^2)^2(1+q^2)}8.
   $$

   The first term contributes $F_0$ and $3q^2A^2/4$ to the coefficient of $s$; $3br^3$ adds $3A^3/8$. The remaining terms start at order $s^7$ or higher. The remainder constant may depend on $k$.

   The unique leading maximiser is $q_0=\sqrt{3/5}$, with $F_0''(q_0)=-3q_0$ and $F_1'(q_0)=-21q_0/25$. Analyticity near $s=0$ and this nonzero second derivative give the local critical branch; uniform convergence to $F_0$ and its strict maximum place all global maximisers near $q_0$ for sufficiently small $s$. Consequently, for each fixed $k\ge3$,

   $$
   q(H_k,\beta)=\sqrt{3/5}-\frac7{25}\sqrt\beta+O(\beta).
   $$

   This asymptotic argument is proved here in prose, not a separate Lean theorem. It supplies no explicit interval endpoint $\beta_k$.

3. **Proved in prose — the $k=2$ drift reverses.** For the source's $G_6=H_2$, $yz^{k+3}$ has order $s^6$, adding $q^6$ to $F_1$. Its derivative at $q_0$ changes $F_1'(q_0)$ to $33q_0/25$, so the coefficient of $\sqrt\beta$ becomes $11/25>0$. This explains the opposite small-density drift without extending the Lean settlement beyond $H_3$.

4. **Literature reading — separate conjectures and the STK proposal.** Conjecture 1 concerns the extremal value and is separate from the monotonicity of the parameter. Zeng, *Finite-Kernel Extremizers in Sparse Extremal Graph Counting*, [arXiv:2606.23737](https://arxiv.org/abs/2606.23737), Theorem 1.2, settles the sparse threshold conjecture reformulated as that paper's Conjecture 1.1, corresponding to Day–Sarkar Conjecture 3. The source's proposed STK classification presumes Conjecture 2; the types of $H_k$ for $k\ge3$ require re-examination. Neither this refutation nor the finite experiment settles Conjecture 1 or provides those types.

5. **Computed — finite readings.** The experiment entry above covers the listed twelve closed-form comparisons, the symbolic $H_3$ derivative, the two exact root-sign checks and the twenty sampled grid/Newton candidates. These readings support the mechanism within exactly that scope.

6. **Open — neighbouring monotonicity questions.** Whether every graph without a pendant-star configuration admits a monotone selection remains open. Whether $q(H_k,\beta)$ is monotone on $(0,\beta_k)$ for some explicit $\beta_k$ remains open. No numerical sample or asymptotic remainder supplies such an explicit endpoint.

## ASSUMED-UNVERIFIED

The source and literature checks recorded in preregistration [#15853](https://github.com/the-omega-institute/trureturing/issues/15853) establish the searched scope, not an exhaustive priority claim. The two-density $H_3$ refutation and the general three-class limit are kernel evidence; the fixed-$k$ asymptotic argument is prose evidence, and the grid/Newton values are computed candidates. Four-slot escape registration is unfinished under #15978.
