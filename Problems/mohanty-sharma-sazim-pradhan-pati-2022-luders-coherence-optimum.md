---
slug: mohanty-sharma-sazim-pradhan-pati-2022-luders-coherence-optimum
bibkey: mohantysharmasazimpradhanpati2022coherence
doi: 10.1007/s11128-021-03394-5
url: https://arxiv.org/abs/2004.10875v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.result
---

# The attained coherence optimum for finite qubit Lüders measurements

## Problem

S. D. Mohanty, G. Sharma, Sk Sazim, B. Pradhan and A. K. Pati, *Creation of quantum coherence with general measurement processes*, Quantum Information Processing 21, 48 (2022), arXiv:2004.10875v2, Section 3.2, `coh-measure.tex`, line 298:

> We couldn't get the expression for $\max_{\{\vec{a},a_{\pm}\}}C_{l_1}(\rho'_{\pm})$ analytically, so we have plotted it against the initial state coherence $C_{l_1}(\rho_{\pm})$.

The same line asks:

> However in this case, we don't know yet for which states there can not be any coherence gain and for which states the coherence gain will be maximum.

The Conclusion, line 505, states:

> As a future line of work, it would be interesting to obtain the analytical results for two outcome and n-outcome POVMs.

The source defines $C_{l_1}(\rho)=\sum_{i\ne j}|\rho_{ij}|$ at line 109 and the nonselective action $\rho\mapsto\sum_i\sqrt{E_i}\rho\sqrt{E_i}$ at lines 127–130, for positive semidefinite effects with $\sum_i E_i=I$. The [literature note](../Library/QuadraticForms/mohantysharmasazimpradhanpati2022coherence.md) records these definitions and the restricted one-parameter result of Section 3.1, lines 230–231:

> ${\max_{\alpha,\lambda}}C_{l_1}(\rho')=\frac{1}{2}\big(C_{l_1}(\rho)+\sqrt{C_{l_1}(\rho)^2+r_3^2}\big)$.

Issue [#22649](https://github.com/the-omega-institute/trureturing/issues/22649) fixes the general reading. For every complex $2\times2$ density matrix $\rho$ and every integer $n\ge2$, determine the attained maximum over all $n$-outcome POVMs, and characterize zero and maximal optimal gain. This is proved.

Write $C(\rho)=C_{l_1}(\rho)$ and
$R(\rho)=\sqrt{\operatorname{Re}(\rho_{00}-\rho_{11})^2+4|\rho_{01}|^2}$, the module's `blochNorm`. Define $L=(C(\rho)+R(\rho))/2$ and $G=L-C(\rho)$. The exact statement is that $L$ is the greatest element of
$\{C(\sum_{i<n}\sqrt{E_i}\rho\sqrt{E_i}):E_i\succeq0,\ \sum_{i<n}E_i=I\}$,
that $G=0$ exactly when $\rho_{00}=\rho_{11}$, that $G\le1/2$, and that $G=1/2$ exactly when $\rho=\operatorname{diag}(1,0)$ or $\rho=\operatorname{diag}(0,1)$.

## Motivation

The optimization distinguishes states whose coherence a measurement can increase from states for which it can only preserve or reduce coherence. A greatest element supplies both a universal bound and an actual measurement attaining it. The answer also determines whether allowing more outcomes improves the best possible single-measurement coherence.

## Gap

The literature check recorded in #22649 has the following scope:

- The orchestrator read the v2 TeX question, checked Crossref's one citing-work count and Semantic Scholar's two listed citing papers, and reported that the latter concern correlated noise channels and quantum radar rather than this optimization.
- The orchestrator reported a web search for the closed form and coherence creation by general measurements, with hits on the source and on different coherence quantities, and no repository record of arXiv:2004.10875.
- The search seat reported searches of Zenodo, ResearchGate, SSRN and GitHub for the title, the quoted question and combinations of Lüders, maximum coherence and two outcomes, without finding a settlement.

`not-found-in-searched-scope`.

## Route

All matrix inputs below are complex $2\times2$ matrices. A density matrix is positive semidefinite with trace one (`IsDensity`); a POVM is a finite family of positive semidefinite matrices summing to the identity (`IsPOVM`). Put $c=\rho_{01}$, $r=\operatorname{Re}(\rho_{00}-\rho_{11})$, $s=2|c|$ and $R=\sqrt{r^2+4|c|^2}$.

1. **Normalized decomposition of the output entry.** For every natural $n$, density matrix $\rho$ and POVM $e:\mathrm{Fin}\,n\to M_2(\mathbb C)$, `luders_decomposition` supplies real $k_i,v_i$ and complex $z_i$ satisfying $k_i\ge0$, $\sum_i[k_i+2(|z_i|^2+v_i^2)]=1$, Hermiticity of the output, and
   $(\operatorname{luders}(e,\rho))_{01}=\sum_i[k_ic+(2\operatorname{Re}(\overline{z_i}c)+v_ir)z_i]$.
   Its construction takes $\sqrt{E_i}=\bigl(\begin{smallmatrix}p_i&z_i\\\overline{z_i}&q_i\end{smallmatrix}\bigr)$, $v_i=(p_i-q_i)/2$ and $k_i=p_iq_i-|z_i|^2$. Positive semidefiniteness gives $k_i\ge0$; the trace and upper off-diagonal entry of $\sum_i(\sqrt{E_i})^2=I$ give the normalization and cancellation.
2. **Quadratic bound.** For arbitrary real $s,r,t,v$, `quadratic_bound` gives $st^2+|r|tv\le\frac{s+\sqrt{r^2+s^2}}2(t^2+v^2)$, by applying `OccupationPartialTransposeSpectral.Scalar.topRoot_quadratic_bound`. For arbitrary complex $c,z$ and real $v,r$, `dephasing_bound` combines this with the norm inequalities to give $2|(2\operatorname{Re}(\overline zc)+vr)z|\le(|z|^2+v^2)(2|c|+\sqrt{r^2+4|c|^2})$; it requires no unit-axis hypothesis.
3. **Universal measurement bound.** For every density matrix $\rho$, `radius_data` gives $0\le C(\rho)\le R(\rho)\le1$ and $R(\rho)^2=r^2+C(\rho)^2$. For every Hermitian matrix $\rho$, `coherence_two` gives $C(\rho)=2|\rho_{01}|$. For every natural $n$, density matrix $\rho$ and POVM $e$ indexed by $\mathrm{Fin}\,n$, `measurement_bound` uses these facts, the decomposition and the triangle inequality to obtain $C(\operatorname{luders}(e,\rho))\le L$. This bound has no hypothesis $n\ge2$.
4. **Attainment.** For arbitrary complex $c$ and real $r$, `optimal_axis` supplies complex $z$ and real $v$ with $|z|^2+v^2=1$ and $|(2\operatorname{Re}(\overline zc)+vr)z|=(2|c|+\sqrt{r^2+4|c|^2})/2$. It handles $R=0$ by $z=1,v=0$; otherwise it chooses a phase $a$ with $|a|=1$, $\overline ac=|c|$, and sets $t=\sqrt{L/R}$, $z=ta$, $v=rt/(2L)$, using $4L(L-s)=r^2$. For complex $z$ and real $v$ satisfying $|z|^2+v^2=1$, `projector_facts` shows that $P=\frac12\bigl(\begin{smallmatrix}1+v&z\\\overline z&1-v\end{smallmatrix}\bigr)$ is a self-adjoint projection. For a density matrix $\rho$ and the same unit-axis condition, `projector_output` evaluates $C(P\rho P+(I-P)\rho(I-P))=|(2\operatorname{Re}(\overline zc)+vr)z|$. For $n\ge2$, any matrices $P,Q,\rho$ with $P,Q$ positive semidefinite and idempotent and $P+Q=I$, `padded_measurement` realizes this output using effects $P,Q$ and $n-2$ zero matrices. Consequently `measurement_attainment`, for every density matrix $\rho$ and integer $n\ge2$, supplies a POVM attaining $L$.
5. **Gain criteria.** For every density matrix $\rho$, `zero_gain` identifies $G=0$ with equality of its diagonal entries, and `maximal_gain` proves $G\le1/2$ with equality exactly for the two stated diagonal matrices. With the same density hypothesis and $n\ge2$, `result` combines attainment and the universal bound into `IsGreatest`, and includes both gain criteria.

## Falsifier

The settlement would not answer the source if it optimized a different measurement rule, coherence convention or outcome class. The module uses:

- the sum of moduli of all off-diagonal entries for `l1Coherence`, so a Hermitian qubit has coherence $2|\rho_{01}|$;
- `luders e ρ` defined as `unreadState` of `CFC.sqrt` of each effect, where `unreadState` is precisely the sum of sandwiches, without outcome selection or extra Kraus unitaries;
- positive semidefinite, trace-one matrices and positive semidefinite effects summing to the identity;
- every family indexed by $\mathrm{Fin}\,n$, including zero effects, with $n\ge2$ for attainment.

In the usual Bloch convention, $\rho_{01}=(r_1-ir_2)/2$ and $r_3=\rho_{00}-\rho_{11}$, so $R(\rho)=|\vec r|$ and equality of the diagonal entries is $r_3=0$. `IsGreatest` includes membership in the output-coherence set as well as an upper bound; no nonemptiness or boundedness assumption is hidden in an infimum or supremum definition.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.lean`.

- **Proof.** It proves `result`, the attained-maximum statement and three gain clauses displayed under Problem.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.lean.json`.

Declaration statements:

- `result`: `sha256:10a50362d733bf3948368de0db0b19de3b800c2e8c2f7f7620d515e353324e39`.

## Triage

Tier 1 question of a 2022 Quantum Information Processing paper and its arXiv version, preregistered in issue #22649 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every complex $2\times2$ positive semidefinite matrix $\rho$ of trace one and every integer $n\ge2$, $(C(\rho)+R(\rho))/2$ is the greatest attainable output coherence over all $n$-outcome POVMs; the optimal gain vanishes exactly when $\rho_{00}=\rho_{11}$, is at most $1/2$, and equals $1/2$ exactly for $\operatorname{diag}(1,0)$ and $\operatorname{diag}(0,1)$.

**Computed, not formalized** (orchestrator, recorded in #22649): random qubit states and measurements were checked numerically before preregistration.

**Argued, not formalized.**

- *Decisive mechanism and sharpness.* For a density matrix $\rho$ and any finite qubit POVM, `luders_decomposition` supplies weights $w_i=k_i+2(|z_i|^2+v_i^2)\ge0$ summing to one, and `measurement_bound` bounds twice the modulus of each output-entry summand by $w_iL$. The triangle inequality therefore bounds output coherence by $\sum_iw_iL=L$. For a density matrix $\rho$ and any $n\ge2$, `measurement_attainment` reaches that bound with a complementary projective pair and zero effects. Thus the gain in allowing arbitrary finite outcomes is already exhausted by an appropriate two-outcome projective measurement; increasing $n$ cannot improve the optimum. These helper statements do not classify all maximizing POVMs.
- *Nonzero effects.* For a positive integer $m$, splitting a nonzero orthogonal projection $P$ into $m$ positive scalar multiples $\alpha_jP$, with $\alpha_j>0$ and $\sum_j\alpha_j=1$, preserves its contribution: $\sqrt{\alpha_jP}=\sqrt{\alpha_j}P$, hence $\sum_j\sqrt{\alpha_jP}\rho\sqrt{\alpha_jP}=P\rho P$. The attaining projection in the route has trace one, and its complement also has trace one, so both are nonzero. Splitting one into $n-1$ equal parts gives an attaining POVM with exactly $n$ nonzero effects for every $n\ge2$. Thus forbidding zero effects alone does not force strict decay with outcome count; optimization with no two proportional effects is open here.
- *Effect on the outcome-count conjecture.* Section 3.3, `coh-measure.tex`, line 321, states: “The quantum coherence induced by an $n$-outcome POVM measurement decreases with increasing $n$.” If this means strict decrease of the unrestricted optimum, the constant optimum in `result` excludes that reading; if it means only nonincrease, a constant optimum is compatible with it. The sample maxima reported for randomly generated POVMs with $n\le20$ in Section 3.3 need not equal the unrestricted maxima, because sampling need not find an attaining POVM. Their reported exponential trend is not reproduced or explained by this settlement.
- *Effect on the other source statements.* The analytical future-work question for a single nonselective qubit Lüders measurement is answered, and the formula and gain criteria given for the restricted family in Section 3.1 extend to all finite POVMs. The later coherence-non-generating-measurement classification and coherence–entanglement trade-off do not assume a solution to the missing optimization; this module does not revalidate those results. The numerical discussion of successive measurements in Section 3.4.1 and the higher-dimensional extension requested in the Conclusion are outside `result`. An exact optimum for successive measurements and a higher-dimensional analogue remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The Crossref and Semantic Scholar readings, the cited-paper assessments and the web searches are reported by the orchestrator in #22649; the Zenodo, ResearchGate, SSRN and GitHub searches are search-seat reports. These searches and the numerical check in that issue have not been independently reproduced here. The source reading is the arXiv v2 TeX, not an independent comparison against the journal text.

The computations and arguments labelled “not formalized” are outside the type of `result`. This includes the nonzero-effect refinement, the interpretation of the source's outcome-count conjecture and the dependency assessment of its later results. The module gives no general-instrument, selective-measurement, higher-dimensional or successive-measurement optimization, and no classification of all maximizers or solution under a restriction excluding proportional effects.
