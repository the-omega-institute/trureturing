---
slug: morelli-yamasaki-huber-tavakoli-2022-imprecise-chsh-optimum
bibkey: morelliyamasakihubertavakoli2022imprecise
doi: 10.1103/PhysRevLett.128.250501
url: https://arxiv.org/abs/2202.13131v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.result
---

# The separable CHSH optimum under imprecise qubit measurements is attained

## Problem

S. Morelli, H. Yamasaki, M. Huber and A. Tavakoli, *Entanglement detection with imprecise measurements*, Phys. Rev. Lett. 128, 250501 (2022), arXiv:2202.13131v2, main text, `Manuscript_epsilonEW.tex`, line 111:

> However, as we show in Supplementary Material through an explicit separable model that we conjecture to be optimal, this fact does not qualitatively improve the robustness of idealised ($\varepsilon=0$) entanglement detection to small inaccuracies.

The witness and candidate value are given at lines 111–115; the supplement, Section “Entanglement detection based on the CHSH quantity” (`AppCHSH`, lines 232–256), specifies two qubits, targets $X=\sigma_X$ and $Z=\sigma_Z$ on both sites, and a common inaccuracy bound $\varepsilon$. See [the literature note](../Library/QuadraticForms/morelliyamasakihubertavakoli2022imprecise.md).

In the formal statement, each of $A_1,A_2,B_1,B_2$ is a complex $2\times2$ matrix satisfying `IsBinaryObservable`: it is Hermitian and $I-A$ and $I+A$ are positive semidefinite. `Admissible` additionally requires

$\operatorname{Re}\operatorname{Tr}(A_1X),\operatorname{Re}\operatorname{Tr}(A_2Z),\operatorname{Re}\operatorname{Tr}(B_1X),\operatorname{Re}\operatorname{Tr}(B_2Z)\ge 2-4\varepsilon$.

`Separable` means membership in the real convex hull of $\sigma\otimes\tau$, where $\sigma,\tau$ are positive semidefinite complex $2\times2$ matrices with trace one. The witness is

$W(\rho;A_1,A_2,B_1,B_2)=\operatorname{Re}\operatorname{Tr}[\rho(A_1\otimes B_1+A_1\otimes B_2+A_2\otimes B_1-A_2\otimes B_2)]$.

Put $\varepsilon_0=\frac12-\frac1{2\sqrt2}$. The definition `separableValue` is the source's candidate:

- for $\varepsilon\le\varepsilon_0$, $V(\varepsilon)=4(1-2\varepsilon)\sqrt{\varepsilon(1-\varepsilon)}+\sqrt{2-16\varepsilon(1-\varepsilon)(1-2\varepsilon)^2}$;
- for $\varepsilon>\varepsilon_0$, $V(\varepsilon)=2$.

Issue [#22442](https://github.com/the-omega-institute/trureturing/issues/22442) fixes the reading: for every $\varepsilon\in[0,1]$, $V(\varepsilon)$ is a greatest element of the set of witness values attained by separable states and admissible observables. This is `claim`, proved by `result : claim`. Greatestness includes both attainment and an upper bound on every value in that set.

## Motivation

The source studies entanglement detection with operationally bounded measurement inaccuracies. For its two-qubit CHSH witness, an explicit separable construction supplies an attainable value. Optimality determines the sharp corrected separable threshold, including whether mixed states or nonprojective binary measurements can exceed that construction under the same constraints.

## Gap

The bounded literature check recorded in #22442 reports:

- the source's v2 TeX retains the optimality conjecture;
- the orchestrator reports no settlement in Cao et al. (2024), arXiv:2310.11946v2, or Sun, Song and Yu (2026), arXiv:2508.03525v2, which concern multipartite witnesses and coarse calibration, respectively;
- the search worker reports screening 25 citing arXiv full texts and finding no settlement, and reports no matching MathDB or formal-conjectures entry;
- the orchestrator reports no related Zenodo record for its search and no earlier repository settlement.

The recorded outcome is `not-found-in-searched-scope`.

## Route

The following are the module's private proof lemmas; all matrices in the local and product statements are complex qubit matrices.

1. **Local ellipse domination.** For real $c,s\ge0$ with $s\le c$ and $c^2+s^2=1$, a positive semidefinite $\sigma$ with $\operatorname{Tr}\sigma=1$, and binary $A_1,A_2$ satisfying $\operatorname{Re}\operatorname{Tr}(A_1X)\ge2c$ and $\operatorname{Re}\operatorname{Tr}(A_2Z)\ge2c$, `local_ellipse_domination` supplies real $u,v$ with $u^2+v^2=1$ and $|\operatorname{Re}\operatorname{Tr}(\sigma A_1)|\le cu+sv$, $|\operatorname{Re}\operatorname{Tr}(\sigma A_2)|\le su+cv$.
2. **Scalar CHSH bound.** For real $c,s\ge0$ with $c^2+s^2=1$, real $u,v,w,z$ with $u^2+v^2=w^2+z^2=1$, and real $\alpha_1,\alpha_2,\beta_1,\beta_2$ satisfying $|\alpha_1|\le cu+sv$, $|\alpha_2|\le su+cv$, $|\beta_1|\le cw+sz$ and $|\beta_2|\le sw+cz$, `dominated_ellipse_chsh` gives $\alpha_1\beta_1+\alpha_1\beta_2+\alpha_2\beta_1-\alpha_2\beta_2\le2cs+\sqrt{1+(c^2-s^2)^2}$.
3. **Small-inaccuracy product bound.** For $\varepsilon\in[0,1]$ with $\varepsilon\le\varepsilon_0$, positive semidefinite $\sigma,\tau$ of trace one, and four `Admissible` observables at $\varepsilon$, `product_upper_small` proves $W(\sigma\otimes\tau;A_1,A_2,B_1,B_2)\le V(\varepsilon)$. Its choices $c=1-2\varepsilon$ and $s=2\sqrt{\varepsilon(1-\varepsilon)}$ satisfy the hypotheses of the local domination lemma, and its scalar bound is exactly the first branch of $V$.
4. **The constant product bound.** For positive semidefinite $\sigma,\tau$ of trace one and any four binary observables, `product_upper_two` proves $W(\sigma\otimes\tau;A_1,A_2,B_1,B_2)\le2$ without calibration hypotheses.
5. **Convex extension.** For fixed arbitrary qubit matrices $A_1,A_2,B_1,B_2$ and a real $K$, if $W(\sigma\otimes\tau;A_1,A_2,B_1,B_2)\le K$ for every pair of positive semidefinite trace-one qubit matrices $\sigma,\tau$, `convex_extension` gives the same bound for every $\rho$ satisfying `Separable`. This supplies the upper bound on the full state set in `claim`.
6. **Attainment.** For any real $c,s$ with $c^2+s^2=1$, `xz_attainment` constructs a positive semidefinite trace-one $\sigma$ such that $A_1=B_1=cX+sZ$, $A_2=B_2=sX+cZ$ on $\sigma\otimes\sigma$ give $2cs+\sqrt{1+(c^2-s^2)^2}$. For $\varepsilon\in[0,1]$ and $\varepsilon\le\varepsilon_0$, `attainment_small` uses the choices in item 3 to obtain a separable state, admissible observables and witness value $V(\varepsilon)$. For every real $\varepsilon>\varepsilon_0$, `attainment_large` constructs a separable product state attaining $V(\varepsilon)=2$ with all four observables $(X+Z)/\sqrt2$.

## Falsifier

The statement would not settle the registered reading if its admissible set restricted lab measurements to projectors, its state set omitted separable mixtures, or its value were only an upper bound without attainment. The definitions and `IsGreatest` conclusion explicitly address these points.

The source-to-matrix correspondence is as follows. A Hermitian $A$ has $I\pm A$ positive semidefinite exactly when every eigenvalue lies in $[-1,1]$, equivalently when its operator norm is at most one. Its two POVM effects are $E_\pm=(I\pm A)/2$; conversely, two positive effects summing to $I$ give such an $A=E_+-E_-$. For $T=X$ or $Z$ and target effects $(I\pm T)/2$, the source's average fidelity is $\mathcal F=\frac12+\frac14\operatorname{Re}\operatorname{Tr}(AT)$, so $\mathcal F\ge1-\varepsilon$ is exactly the calibration inequality used in `Admissible`. These are explanatory finite-dimensional identifications, not additional conclusions stated by `result`.

## Evidence

The canonical source is `D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.lean.json`.

Declaration statements:

- `result`: `sha256:5cdc26dc072c30ffc378911c3a80b29268d2b2b25f493b9d1b74223bbea79334`;
- `claim`: `sha256:11c4a887058e532e179548c859aa47fbca61d56e2b5fe81d89bd1dede3783a50`.

## Triage

Tier 1 conjecture of a 2022 Phys. Rev. Lett. paper, preregistered in issue #22442 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $\varepsilon\in[0,1]$, $V(\varepsilon)$ is a greatest element of the set of real witness values obtained from `Separable` two-qubit matrices and four observables satisfying `Admissible` at $\varepsilon$: some such choice attains $V(\varepsilon)$, and every such choice has witness value at most $V(\varepsilon)$.

**Computed, not formalized.**

- At $\varepsilon=0.005$, direct evaluation of the displayed formula gives $V(\varepsilon)\approx1.66566976236$.

**Argued, not formalized.**

- *Decisive mechanism and sharpness.* For real $c,s\ge0$ with $s\le c$ and $c^2+s^2=1$, a positive semidefinite trace-one qubit matrix $\sigma$, and binary $A_1,A_2$ with $\operatorname{Re}\operatorname{Tr}(A_1X)\ge2c$ and $\operatorname{Re}\operatorname{Tr}(A_2Z)\ge2c$, `local_ellipse_domination` supplies one common pair $u,v$ with $u^2+v^2=1$ bounding the expectation magnitudes by $cu+sv$ and $su+cv$, respectively. This preserves a relation between the local expectations. By comparison, four independent real expectations in $[-1,1]$ include the choice $(1,1,1,1)$, whose CHSH value is $2$, so those interval constraints alone cannot give a uniform bound below $2$. For the complete admissible set and parameter range in `claim`, greatestness establishes sharpness of the resulting formula.
- *Small-error sensitivity.* For $0<\varepsilon\le\varepsilon_0$, put $r=4(1-2\varepsilon)\sqrt{\varepsilon(1-\varepsilon)}$. Rationalizing the second square root gives $V(\varepsilon)-\sqrt2=r-r^2/(\sqrt{2-r^2}+\sqrt2)$. Here $r/\sqrt\varepsilon\to4$, $r^2/\sqrt\varepsilon\to0$, and the denominator tends to $2\sqrt2$ as $\varepsilon\to0^+$, so $(V(\varepsilon)-\sqrt2)/\sqrt\varepsilon\to4$. In particular the right difference quotient at zero diverges to positive infinity. This derives the leading square-root sensitivity of the exact optimum discussed by Morelli, Yamasaki, Huber and Tavakoli (2022), arXiv:2202.13131v2, lines 115 and 256.
- *Unequal error bounds.* If the four devices have individual bounds $\varepsilon_i\in[0,1]$, put $\varepsilon=\max_i\varepsilon_i$. Each calibration inequality at $\varepsilon_i$ implies the corresponding inequality at $\varepsilon$, since $2-4\varepsilon_i\ge2-4\varepsilon$. Every separable witness value for these stronger individual constraints is therefore at most $V(\varepsilon)$. Attainment for this smaller feasible set does not follow from `result`; its sharp optimum is not determined here.
- *Effect on the source.* Under the two-qubit, binary-observable and calibration hypotheses in `claim`, an observed witness value above $V(\varepsilon)$ excludes `Separable`, since it contradicts the proved upper bound. The conjectural optimality qualification on this CHSH threshold can therefore be removed for the registered reading, and the source's qualitative small-inaccuracy sensitivity concerns the exact optimum. The source's other witnesses, higher-dimensional tightness question involving SIC-POVMs, entangled values and SDP methods are outside this result, as are its general-correction, auxiliary-setting and multipartite questions at lines 182–183.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The two follow-ups' arXiv metadata and abstracts confirm their identities and stated topics; the full-text findings of no settlement, 25 citing-text screening, MathDB and formal-conjectures searches, and Zenodo search are reports in #22442, not independently reproduced literature checks. The source quotation, calibration framework and candidate formula are checked against the v2 TeX source.

The source-to-matrix identifications in `Falsifier`, the numerical evaluation, and the arguments in `Triage` are not additional formalized declarations. `result` proves the optimal value and existence of attaining matrices; it does not identify its algebraic attaining state with the supplement's literal trigonometric state parametrization, whose boundary convention is not separately verified. The source's numerical and SDP studies are not reproduced. Unequal-error sharpness, other targets, higher dimensions, other witnesses, entangled optima and experimental verification of the calibration premises remain outside this settlement.
