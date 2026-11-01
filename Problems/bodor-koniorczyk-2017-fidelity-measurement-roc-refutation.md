---
slug: bodor-koniorczyk-2017-fidelity-measurement-roc-refutation
bibkey: bodorkoniorczyk2017quantumroc
doi: 10.1007/s10946-017-9629-5
url: https://arxiv.org/abs/1603.06801v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result
---

# The Fuchs–Caves fidelity measurement need not give optimal ROC points

## Problem

A. Bodor and M. Koniorczyk, *Receiver operation characteristics of quantum state discrimination* (J. Russ. Laser Res. 38, 150–163, 2017; arXiv:1603.06801v1), ask whether the cumulative points of the fidelity measurement lie on the optimal receiver operating characteristic (ROC) curve. The v1 TeX member `Bodor_Koniorczyk_QuantumROC_submit_1.tex`, lines 940–944, in the subsection “The quantum Bhattacharyya coefficient”, states:

> This obviously defines $d+1$ points in the feasible ROC domain, where $d$ stands for the dimension of the joint support of the two density operators. (It is an interesting open question whether these points are actually on the optimal ROC curve.)

The observable in the preceding equation, labelled `eq:fidelitymeasurable`, is
$$M=(\sqrt{\rho})^{-1}\sqrt{\sqrt{\rho}\,\sigma\sqrt{\rho}}\,(\sqrt{\rho})^{-1},$$
where $\rho=\varrho_N$ and $\sigma=\varrho_P$. For an ordered orthonormal eigenbasis $(a_i)_{i=0}^{d-1}$, put $q_i=\operatorname{Re}(a_i^\dagger\rho a_i)$ and $p_i=\operatorname{Re}(a_i^\dagger\sigma a_i)$, ordered by nonincreasing $p_i/q_i$, and define $Q_k=\sum_{i<k}q_i$, $P_k=\sum_{i<k}p_i$.

Issue [#24220](https://github.com/the-omega-institute/trureturing/issues/24220) fixes the universal reading: for every finite dimension $d$, every pair of positive-definite trace-one complex matrices $\rho,\sigma$, every such ordered eigenbasis, and every $0\le k\le d$, every binary effect $0\le F\le I$ satisfying $\operatorname{Re}\operatorname{tr}(F\rho)=Q_k$ must satisfy $\operatorname{Re}\operatorname{tr}(F\sigma)\le P_k$. This is `claim`; `result` refutes it.

The definitions and source locators are collected in [the literature note](../Library/Observer/bodorkoniorczyk2017quantumroc.md).

## Motivation

The question asks whether one measurement selected to attain fidelity also supplies optimal binary discriminators at all its cumulative thresholds. An affirmative answer would provide distinguished samples of the quantum ROC boundary from a single observable. The source raises the question inside its comparison between the quantum Bhattacharyya coefficient and square-root fidelity; separating boundary optimality from fidelity attainment clarifies what that comparison requires.

## Gap

Issue #24220 records the bounded literature check supporting the preregistration:

- arXiv listed only v1, whose TeX retains the question;
- searches by title, authors, ROC, fidelity measurement and optimal ROC curve found the source and related work on quantum binary hypothesis testing, without a settlement in the searched scope;
- the reported OpenAlex listing contained three citations to the journal version and none to the preprint, and the reported reading of arXiv:2012.08081 found no answer to this question;
- the full text of the related monograph, DOI 10.1561/2000000106, was not retrieved;
- the repository searches recorded in the issue found no prior preregistration or matching D5 result.

`not-found-in-searched-scope`.

## Route

All private lemma names below belong to `FidelityMeasurementROCRefutation` unless another module is named. The witness is the fixed three-dimensional pair
$$\rho=\frac1{20}\begin{pmatrix}2&1&1\\1&10&1\\1&1&8\end{pmatrix},\qquad
\sigma=\frac1{40}\begin{pmatrix}16&4&2\\4&20&1\\2&1&4\end{pmatrix},\qquad
D=\operatorname{diag}(2,1,1/2).$$

1. **States.** `rho_posDef` uses $20\rho=J+\operatorname{diag}(1,9,7)$, with $J$ the positive-semidefinite all-ones matrix. For these fixed matrices, `diagonal_posDef` gives $D>0$, `sigma_eq` gives $\sigma=D\rho D$, and `sigma_posDef` gives $\sigma>0$. `rho_trace` and `sigma_trace` give both traces equal to one.
2. **The observable and basis.** `sqrt_observable` identifies $M=D$ for this pair. It applies `AlternativeMeanLinearization.riccati_unique`, whose hypotheses are $A>0$, $Y>0$ and $YAY=B$, with $A=\rho$, $Y=D$ and $B=\sigma$. `coordinate_basis_ordered` certifies the coordinate vectors as normalized, pairwise orthogonal eigenvectors with real eigenvalues and the required likelihood-ratio ordering. `cumulative_first_rho` and `cumulative_first_sigma` give their first cumulative point as $(Q_1,P_1)=(1/10,2/5)$.
3. **A better binary test.** For the fixed vector $v=(37,2,-3)^{\mathsf T}$, `competitor_eq` identifies the competing matrix as $F=vv^\dagger/1382$, and `competitor_binary` certifies $0\le F\le I$. `competitor_rho_trace` and `competitor_sigma_trace` give
   $$\operatorname{Re}\operatorname{tr}(F\rho)=\frac1{10},\qquad
   \operatorname{Re}\operatorname{tr}(F\sigma)=\frac{5539}{13820}>\frac25.$$
   Applying `claim` at $d=3$, this pair, the coordinate basis and $k=1$ would require the opposite weak inequality. `result` derives the contradiction.

## Falsifier

The witness would not answer the question if the observable, basis ordering, cumulative coordinates or allowed competing tests differed from the source's. The module uses the positive-square-root formula above, orthonormal eigenvectors, and cross-multiplied likelihood ordering $p_iq_j\ge p_jq_i$ for $i\le j$. Positive definiteness makes every $q_i$ positive, so this is precisely decreasing likelihood-ratio order. Its `readout` is the real part of the quadratic form, and `onOptimalROC` compares against all matrix effects in the positive-semidefinite order interval $[0,I]$ at exactly the same false-positive coordinate.

The source TeX displays $P_k=\sum_{l=1}^k p_k$ and $Q_k=\sum_{l=1}^k q_k$ at lines 386 and 391. The formal reading uses the outcome-by-outcome cumulative sums described in the surrounding text. At $k=1$ the displayed and cumulative readings agree, so this indexing discrepancy does not affect the witness.

Both witness states are positive definite on the whole three-dimensional space, which is their joint support. The counterexample therefore lies within the source's setting without any singular-inverse convention. A single feasible competing effect suffices; no evaluation of a supremum or infimum is needed. The conclusion negates universal optimality, not optimality of every cumulative point for every pair.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:b9715de3d392e370bccfa1bd2d0ad38ddc3dc31c6a1d346da050d8092a93f479`;
- `claim`: `sha256:3cac0ac7897f4ddfaf92691ff925e7f7808256deaad1c2e5886552370fd210b8`.

## Triage

Tier 1 question of a 2016 preprint published in 2017, preregistered in issue #24220 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every finite dimension, every pair of positive-definite trace-one complex matrices, every ordered orthonormal eigenbasis of their fidelity observable and every cumulative index, all binary effects at the same false-positive coordinate have true-positive coordinate at most that cumulative true-positive coordinate.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Mechanism.* For the fixed positive-definite witness, `sigma_eq` and `sqrt_observable` give the congruence relation $\sigma=M\rho M$, whereas ROC optimization at a supporting slope $t$ concerns the linear operator $\sigma-t\rho$. Its $(0,1)$ and $(0,2)$ entries are $(2-t)/20$ and $(1-t)/20$, so no $t$ makes it diagonal in the coordinate fidelity basis. For this pair, `coordinate_basis_ordered` certifies the ordered fidelity eigenbasis, while `competitor_binary`, `competitor_rho_trace` and `competitor_sigma_trace` certify a better effect at its first false-positive coordinate. Thus neither full support nor the required likelihood ordering supplies the missing boundary-optimality condition.
- *A sufficient structure.* For any positive-definite trace-one pair and any $t\ge0$, an effect maximizing $\operatorname{Re}\operatorname{tr}(F(\sigma-t\rho))$ is ROC-optimal at its own false-positive coordinate: every effect with that coordinate has the same subtracted term. Diagonalizing the Hermitian matrix $H=\sigma-t\rho$ gives $\operatorname{tr}(FH)=\sum_j\lambda_j\langle u_j,Fu_j\rangle\le\sum_{\lambda_j>0}\lambda_j$, because each diagonal entry of an effect lies in $[0,1]$. Equality is attained by identity on the positive spectral subspace and zero on the negative one, with arbitrary effect on the kernel. The fidelity eigenbasis condition alone does not impose this sign-subspace alignment on each cumulative projector.
- *A surviving restriction.* For commuting positive-definite trace-one states measured in a common eigenbasis, all cumulative likelihood thresholds are ROC-optimal. In that basis both states are diagonal, so every competing effect contributes only its diagonal entries $f_i\in[0,1]$. Let $b_i=1$ for $i<k$ and zero otherwise. Choose $t$ between the adjacent ordered ratios, taking $t\ge\max_i(p_i/q_i)$ at $k=0$ and $t=0$ at $k=d$. At the same false-positive coordinate, $\sum_iq_i(f_i-b_i)=0$, and therefore
  $$\sum_i p_i(f_i-b_i)=\sum_i(p_i-tq_i)(f_i-b_i)\le0.$$
  Every summand is nonpositive: on the selected indices its two factors have signs $\ge0$ and $\le0$, and on the others their signs reverse. This is a classical threshold argument, not an additional theorem of the module.
- *Unsettled scope.* A classification of optimal cumulative points for noncommuting pairs, the smallest possible counterexample dimension and the exact ROC optimum for this witness are not determined here.
- *Effect on the paper.* The adjoining proposition states: “The quantum Bhattacharyya coefficient is lower than or equal to the square root fidelity. It is equal if and only if the two density operators commute.” (v1 TeX, lines 926–929.) Its length-comparison argument uses the fidelity polyline's feasibility and its position below the optimal curve; it does not require an affirmative answer to the question about its vertices. The refutation rules out treating these vertices as universal samples of the optimal curve. It neither refutes nor formalizes that coefficient proposition, its equality criterion, the source's completely-positive-map monotonicity proposition, or the separate unital-map conjecture at lines 974–977.

## ASSUMED-UNVERIFIED

The bounded literature check in #24220 does not establish exhaustive worldwide novelty or priority. Its web and repository searches, arXiv version inventory, OpenAlex citation counts and reported reading of arXiv:2012.08081 were not independently reproduced. The full text of the monograph DOI 10.1561/2000000106 was not read, and the journal text was not compared with arXiv v1.

The statements in “Argued, not formalized” are not formalized; the commuting restriction and spectral supporting-line argument are mathematical arguments, not additional compiled declarations. The coefficient propositions and unital-map conjecture remain outside this settlement.
