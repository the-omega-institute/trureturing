---
slug: mohanty-sharma-sazim-pradhan-pati-2022-luders-coherence-optimum
bibkey: mohantysharmasazimpradhanpati2022coherence
doi: 10.1007/s11128-021-03394-5
url: https://arxiv.org/abs/2004.10875v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.result
---

# The attained coherence optimum for arbitrary finite qubit Lüders measurements

## Problem

S. D. Mohanty, G. Sharma, Sk Sazim, B. Pradhan and A. K. Pati, *Creation of quantum coherence with general measurement processes*, Quantum Information Processing 21, 48 (2022), arXiv:2004.10875v2, Section 3.2, `coh-measure.tex`, line 298:

> We couldn't get the expression for $\max_{\{\vec{a},a_{\pm}\}}C_{l_1}(\rho'_{\pm})$ analytically, so we have plotted it against the initial state coherence $C_{l_1}(\rho_{\pm})$.

> However in this case, we don't know yet for which states there can not be any coherence gain and for which states the coherence gain will be maximum.

The Conclusion, line 505, asks:

> As a future line of work, it would be interesting to obtain the analytical results for two outcome and n-outcome POVMs.

The source defines $C_{l_1}(\rho)=\sum_{i\ne j}|\rho_{ij}|$ at line 109 and the nonselective Lüders action $\Phi_E(\rho)=\sum_i\sqrt{E_i}\rho\sqrt{E_i}$ at lines 127–130. A qubit density matrix is a positive semidefinite complex $2\times2$ matrix of trace one; an $n$-outcome POVM is a family of positive semidefinite effects indexed by $\mathrm{Fin}\,n$ whose sum is $I$.

Put $s=C_{l_1}(\rho)$, $R=\sqrt{(\operatorname{Re}(\rho_{00}-\rho_{11}))^2+4|\rho_{01}|^2}$ and $\lambda=(s+R)/2$. Issue [#22649](https://github.com/the-omega-institute/trureturing/issues/22649) fixes the statement: for every qubit density matrix and every integer $n\ge2$, $\lambda$ is the attained greatest output coherence; the optimal gain $\lambda-s$ vanishes exactly when $\rho_{00}=\rho_{11}$, is at most $1/2$, and equals $1/2$ exactly for $\operatorname{diag}(1,0)$ and $\operatorname{diag}(0,1)$. This is proved.

The definitions and source locators are also in [the literature note](../Library/QuadraticForms/mohantysharmasazimpradhanpati2022coherence.md).

## Motivation

The paper asks how much coherence a measurement can create when its outcome is discarded. Section 3.1 solves a restricted one-parameter family; Section 3.2 leaves the general two-outcome optimization and its extremal states undetermined. An attained optimum over every finite POVM distinguishes the limits imposed by the Lüders rule from the performance of a chosen family or random sample.

## Gap

Issue #22649 records the bounded literature check before any Lean:

- the v2 TeX states the analytic question and the finite-outcome future work;
- the orchestrator records one citing work from Crossref and two citing papers from Semantic Scholar, concerning correlated noise channels and quantum radar, with neither treating this question;
- the orchestrator's web searches returned the source and work on different coherence quantities;
- the search contributor, identified there as the nyxid-oracle ChatGPT Pro search, reports no settlement in searches of Zenodo, ResearchGate, SSRN and GitHub;
- the orchestrator reports no existing repository issue, module, Library note or dossier for arXiv:2004.10875.

`not-found-in-searched-scope`.

## Route

The lemma names below belong to `LudersCoherenceCreationOptimum` unless qualified otherwise.

1. **Coordinates.** For any Hermitian complex $2\times2$ matrix, `coherence_two` gives $C_{l_1}(\rho)=2|\rho_{01}|$. For a qubit density matrix, `radius_data` gives $0\le s\le R\le1$ and $R^2=r^2+s^2$, where $r=\operatorname{Re}(\rho_{00}-\rho_{11})$.
2. **A normalized decomposition of the output entry.** For every natural $n$, qubit density matrix $\rho$ and $n$-outcome POVM $E$, `luders_decomposition` supplies $k_i\ge0$, complex $z_i$ and real $v_i$ satisfying $\sum_i[k_i+2(|z_i|^2+v_i^2)]=1$. The output is Hermitian and, writing $c=\rho_{01}$, its upper off-diagonal entry is $\sum_i[k_ic+(2\operatorname{Re}(\overline{z_i}c)+v_ir)z_i]$. In its proof, $k_i=p_iq_i-|z_i|^2$ and $v_i=(p_i-q_i)/2$ for the diagonal entries $p_i,q_i$ of $\sqrt{E_i}$; positivity gives $k_i\ge0$ and completeness cancels the remaining linear term.
3. **The quadratic bound.** For all real $s,r,t,v$, `quadratic_bound` gives $st^2+|r|tv\le\frac{s+\sqrt{r^2+s^2}}2(t^2+v^2)$ by applying `OccupationPartialTransposeSpectral.Scalar.topRoot_quadratic_bound`. For all complex $c,z$ and real $v,r$, `dephasing_bound` consequently gives $2|(2\operatorname{Re}(\bar zc)+vr)z|\le(|z|^2+v^2)(2|c|+\sqrt{r^2+4|c|^2})$. For a qubit density matrix and any finite POVM, `measurement_bound` combines this with $s\le\lambda$, the triangle inequality and the normalized nonnegative coefficients to obtain $C_{l_1}(\Phi_E(\rho))\le\lambda$.
4. **Attainment.** For every complex $c$ and real $r$, `optimal_axis` supplies $z\in\mathbb C$, $v\in\mathbb R$ with $|z|^2+v^2=1$ and $|(2\operatorname{Re}(\bar zc)+vr)z|=(2|c|+\sqrt{r^2+4|c|^2})/2$. Its zero-radius case takes $z=1,v=0$. For $R>0$, it chooses a phase $a$ with $|a|=1$ and $\bar ac=|c|$, and sets $t=\sqrt{\lambda/R}$, $v=rt/(2\lambda)$ and $z=ta$; the identity $4\lambda(\lambda-s)=r^2$ verifies the unit-length and attainment equations. For a qubit density matrix and $n\ge2$, `measurement_attainment` constructs an attaining POVM from two complementary projections and $n-2$ zero effects.
5. **Extremal gain.** For every qubit density matrix, `zero_gain` identifies $\lambda-s=0$ exactly with $\rho_{00}=\rho_{11}$, and `maximal_gain` gives $\lambda-s\le1/2$ and its two diagonal equality cases. Together with the bound and attaining family, these give `result`.

## Falsifier

The settlement would miss the source's question if the coherence, admissible effects or state update differed. Here `l1Coherence` is precisely the sum of off-diagonal moduli, `IsDensity` means positive semidefinite with trace one, and `IsPOVM` imposes positivity and completeness. `luders` uses `CFC.sqrt` of each effect in the sandwiches, matching the positive-root action at source lines 127–130. It does not optimize over instruments with additional outcome-dependent unitaries or over selective outputs.

The outcome convention permits zero effects and repeated effects. The formal optimum is an `IsGreatest` statement: it contains an attaining POVM and bounds every admissible output, without relying on an infimum or supremum of an unverified domain. The quantified conclusion requires $n\ge2$ and dimension two.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.lean`.

- **Proof.** It proves `result`, whose type is the conjunction of the attained greatest-element statement and the three extremal-gain statements above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.lean.json`.

Declaration statements:

- `result`: `sha256:10a50362d733bf3948368de0db0b19de3b800c2e8c2f7f7620d515e353324e39`.

## Triage

Tier 1 question of a 2022 paper and its arXiv version, preregistered in issue #22649 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every qubit density matrix $\rho$ and every integer $n\ge2$:

- $(s+R)/2$ is the greatest element of the set of output coherences of all $n$-outcome POVMs under `luders`, so this value is attained;
- the optimal gain $(s+R)/2-s$ equals zero if and only if $\rho_{00}=\rho_{11}$;
- that optimal gain is at most $1/2$;
- that optimal gain equals $1/2$ if and only if $\rho=\operatorname{diag}(1,0)$ or $\rho=\operatorname{diag}(0,1)$.

**Computed, not formalized** (orchestrator, recorded in issue #22649): random qubit states and measurements were checked numerically before preregistration.

**Argued, not formalized.**

- *Full channel mechanism.* For a qubit density matrix and any finite qubit POVM, write the positive roots as $K_i=a_iI+\mathbf b_i\cdot\boldsymbol\sigma$, with real $a_i\ge|\mathbf b_i|$. Expanding $\sum_iK_i^2=I$ gives $\sum_i(a_i^2+|\mathbf b_i|^2)=1$ and $\sum_i a_i\mathbf b_i=0$. Pauli multiplication gives the output Bloch vector $\mathbf r'=\kappa\mathbf r+2\sum_i\mathbf b_i(\mathbf b_i\cdot\mathbf r)$, where $\kappa=\sum_i(a_i^2-|\mathbf b_i|^2)\ge0$. For each nonzero $\mathbf b_i$, put $\mathbf u_i=\mathbf b_i/|\mathbf b_i|$ and $w_i=2|\mathbf b_i|^2$; zero vectors contribute zero weight. Since $\kappa+\sum_iw_i=1$, the entire channel is a convex combination of the identity and projective dephasings $\mathbf r\mapsto\mathbf u_i(\mathbf u_i\cdot\mathbf r)$. This explains why adding general effects cannot improve on the optimal dephasing. The formal `luders_decomposition` establishes the output-entry statement in the Route for density inputs and finite POVMs; this full-channel interpretation is a separate algebraic argument.
- *Nonzero effects.* For a qubit density matrix and $n\ge2$, the attaining construction in `measurement_attainment` uses complementary projections $p,q$. Their diagonal entries are $(1+v)/2,(1-v)/2$ in opposite orders, so both have trace one and are nonzero. Replace $p$ by $n-1$ copies of $p/(n-1)$ and retain $q$. All effects are nonzero, their sum is $I$, and each new square root is $p/\sqrt{n-1}$. Their combined contribution is $p\rho p$, so the output remains $p\rho p+q\rho q$. Thus requiring nonzero effects, while allowing repeated effects, does not by itself change the optimum; this refinement is not formalized in `result`.
- *The one-outcome boundary.* With one outcome, completeness forces $E_0=I$, so the Lüders output is $\rho$ and the optimum is $s$. The hypothesis $n\ge2$ therefore matters.
- *Effect on the source.* Section 3.3, line 321, states: “The quantum coherence induced by an $n$-outcome POVM measurement decreases with increasing $n$.” If this means strict decrease of the unrestricted optimum, it is incompatible with the constant optimum in `result`; a weak nonincrease reading is compatible with constancy. The exponential trend discussed at lines 314–318 concerns maxima of random samples, whose distribution and sampling behavior are not determined by this theorem. The analytic questions at lines 298 and 505 are settled for a single qubit Lüders measurement, consistently with the restricted-family result at lines 230–237. The entropy-based entanglement trade-off in Section 5, lines 467–495, does not use the outcome-count conjecture and receives no additional certification here. The successive-measurement observation at line 379 and the higher-dimensional question at line 505 remain outside the settlement.

## ASSUMED-UNVERIFIED

The literature check in issue #22649 is bounded and does not establish exhaustive worldwide novelty or priority. Its citation counts, citing-paper readings, web searches and contributor-reported Zenodo, ResearchGate, SSRN and GitHub searches were not independently reproduced. The source quotations and definitions were checked against `coh-measure.tex` from arXiv:2004.10875v2.

The numerical check attributed to the orchestrator was not independently reproduced and provides only numerical evidence. The full-channel interpretation, nonzero-effect refinement, one-outcome boundary and discussion of consequences for the source are not additional formal conclusions of `result`. The explanation of the source's random-sampling trend, successive-measurement optima, higher-dimensional analogues and selective or more general instrument optimizations remain open here.
