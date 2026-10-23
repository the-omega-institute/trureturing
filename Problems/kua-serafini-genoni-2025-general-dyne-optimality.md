---
slug: kua-serafini-genoni-2025-general-dyne-optimality
bibkey: kuaserafinigenoni2025daemonic
doi: 10.1088/2058-9565/ae2200
url: https://arxiv.org/abs/2506.22288
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.result
---

# The aligned general-dyne measurement attains the global steady-state optimum

## Problem

K. H. Kua, A. Serafini and M. G. Genoni, *Daemonic ergotropy of Gaussian quantum states and the role of measurement-induced purification via general-dyne detection*, arXiv:2506.22288v2; Quantum Sci. Technol. 11, 015014 (2026), DOI 10.1088/2058-9565/ae2200, Section VI after Eq. (66), state:

> We have also numerically verified that non-zero phases ϑ_m lead to worse result, and we can thus conjecture that this fully characterizes the optimal steady-state general-dyne monitoring.

The [Library note](../Library/QuantumBounds/kuaserafinigenoni2025daemonic.md) gives the source locators and Eq. (66). Write $r=2\chi/\kappa$, $\nu=2n_{\rm th}+1$ and $c=\sqrt{1-r^2}$, with $\kappa>0$, $0\le\chi<\kappa/2$ and $n_{\rm th}\ge0$. For every finite physical general-dyne measurement covariance $M$ and physical stationary conditional covariance $S$, the result proves

$$\sqrt{\det S}\ge v_* = \frac{(\nu-1)c+\sqrt{(\nu-1)^2c^2+4\nu}}{2}.$$

The pure aligned covariance

$$M_*=\operatorname{diag}\left(\frac{1-r}{1+r},\frac{1+r}{1-r}\right)$$

has a physical stationary solution attaining this value. No uniqueness of the minimizing measurement is asserted by the public theorem.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Stable thermal OPO, Eqs. (57)–(58) | `claim` parameters `κ`, `χ`, `nth` and its four hypotheses; `driftA` | All damping, pump and thermal parameters in the stated regime |
| Thermal input and diffusion | Literal scalar multiples of the identity inside `eMat`, `bMat`, `steadyEq` | $\sigma_{\rm in}=\nu I$ and $D=\kappa\nu I$ |
| Passive coupling in physical q,p coordinates | `coupling` | $C=\sqrt\kappa\,\Omega$, with $\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ |
| Source E and B, Eqs. (21)–(25) | `eMat`, `bMat` | The inverse matrix square root is `CFC.sqrt` of the inverse positive matrix |
| Stationary Riccati equation, Eq. (55) | `steadyEq` | Every matrix product, transpose and diffusion term is retained |
| Every physical measurement and stationary covariance | `claim` first conjunct; frozen `IsGaussianMeasurementCov (m := 1)` | Symmetry and the complex uncertainty matrix being positive semidefinite; arbitrary phase, squeezing and impurity |
| Global optimum | `vStar`; `result` first conjunct | Universal determinant-square-root lower bound |
| Aligned pure measurement, Eq. (66) | `optMeas`; `result` second conjunct | Existence of a physical stationary attainer with equality |

The symplectic, thermal-input and diffusion expressions are inlined in the public formulas. Proofs use the frozen `PositiveOneModeWilliamson.physicalJ2` through `omega_sq`, and the frozen physical covariance predicate and public `GaussianThermometryJointMeasurementRefutation.physical_data`. The finite $2\times2$ real matrix carrier is the source's single-mode covariance representation. Requiring $S$ to be physical restricts the conclusion to conditional covariance solutions; it adds no hypothesis to the source's physical statement. The damping scale cancels without restricting its positive value.

## Motivation

Issue [#16522](https://github.com/the-omega-institute/trureturing/issues/16522) preregisters this tier-1 published conjecture and its literal covariance conventions. The bound includes noisy measurement covariances and every physical stationary solution, rather than only the phase-zero family. Equation (52) makes daemonic ergotropy decrease with $\sqrt{\det S}$ while the unconditional moments are measurement-independent. Thus the covariance optimum supplies the conjectured steady-state ergotropy optimum within the source model; this physical interpretation is not a separate Lean theorem.

## Gap

The source proves the phase-zero optimum and supports the global claim numerically. Its global comparison over all measurement phases and impurities is the mathematical gap. The literal public statement is `claim`, and `result : claim` settles both its universal bound and aligned attainment.

Literature completeness is `ASSUMED-UNVERIFIED`. The source and literature checks recorded by the orchestrator on #16522 cover arXiv v2 and the cited works 2609.24425, 2512.05244, 2511.07243 and 2606.19945; no OPO general-dyne optimum theorem is reported in that screen. The codex-cli research input reports a reading of Liu–Chen, *Projective sufficiency for daemonic ergotropy in arbitrary two-qubit states*, SciPost submission `scipost_202606_00048v1`: its two-qubit setting differs from the thermal OPO, and it does not supply this optimum theorem. That reading is seat-reported, not a claim of an exhaustive literature search.

## Route

The consumed private lemma `source_reduction` transports the source equation to

$$0=\nu I-\frac{D_0S+SD_0}{2}-(S-\nu I)Q(S-\nu I),\qquad D_0=\operatorname{diag}(1+r,1-r),\quad Q=(\nu I+M)^{-1}.$$

The bridge `physical_iff` identifies the one-mode physical domain with $M\succ0$ and $\det M\ge1$. Put $V=S-\nu I$, $R=\nu I-(D_0S+SD_0)/2$ and $N=I-\nu Q$. The stationary equation gives $R=VQV\succeq0$; `n_posDef` proves $N\succ0$, and `covariance_factors` proves $W=VNV\succeq0$ with $\det W=\det M\det R$.

The private determinant, quadratic-form, trace and root lemmas provide an algebraic lower-branch exclusion for positive pump. `zero_pump_covariance` handles the zero-pump boundary. `aligned_attainment` supplies the explicit diagonal attainer; `result` combines the bound and existence conclusions. All 26 helpers are bind-only after expansion into frozen and pinned-Mathlib facts and normalization. The settling module has `admission_basis: open-problem-resolution (#16522; Proved)`, `utility: none`, and `generality: I`.

## Falsifier

A physical measurement $M$ and physical covariance $S$ solving `steadyEq` with $\sqrt{\det S}<v_*$ would contradict the first conjunct. Failure of physicality, stationarity or equality for every covariance at `optMeas` would contradict the second. Both conjuncts are proved together by `result` under the four source hypotheses.

## Evidence

The formal source is [GeneralDyneSteadyStateOptimality.lean](../D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.lean); its canonical [Blueprint mirror](../Blueprint/D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.md) gives every public definition and the complete result. The axiom closure of every public declaration is contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

Escape audit unfinished: [#16704](https://github.com/the-omega-institute/trureturing/issues/16704) covers `GeneralDyneSteadyStateOptimality.result` and the publicized owner theorem `GaussianThermometryJointMeasurementRefutation.physical_data`. No validated four-slot registration is claimed. The complete source-family reconstruction, lawful enrolled readout, realization bridge, variation, sensitivity, observational dependence and binding evidence remain missing.

### Experiment

The experiment is [the pinned directory in trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/tree/ca30f7cb2507de553745b2ab3ef1b80959e84bb7/docs/reports/kua-serafini-genoni-2025-general-dyne-optimality), containing `check.py` with SHA-256 `6fd5785c3fcb989603487e0a1dbfb6207d26e3ec8b999dde0d7667d84c34f02c`. Run `python3 check.py` from that directory: exit 0, `ALL_OK`. The script was read from the pinned Git object and rerun without changing its bytes.

Its exact Sympy checks verify both determinant identities. Its float64 Riccati checks use $r\in\{0.1,0.5,0.9,0.99\}$ and $\nu\in\{1,1.5,3,10\}$, 190 random physical measurements per pair: 3040 random measurements in total, plus the 16 aligned measurements. Every random trial has positive-definite covariance, residual at most $10^{-8}$ and $\sqrt{\det S}\ge v_*-10^{-9}$; aligned trials have residual at most $10^{-9}$ and determinant-square-root error at most $10^{-7}$. This finite numerical scope is not the evidence for the universal theorem.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Correlation, imbalance and impurity decomposition | Proved, kernel-checked | `identity_two`, `covariance_factors`, `trace_bound`, and `positive_branch_lower` establish the displayed identity and nonnegativity used by `result` |
| Strict positive-branch exclusion for $r>0$ | Proved, kernel-checked | `positive_branch_lower` establishes $v\ge\nu c$ and the strictly positive factor $F_+$ |
| Aligned, balanced, pure equality in the nondegenerate regime | Proved in prose below | Requires $r>0$ and $\nu>1$; the Lean public theorem does not classify equality cases |
| Explicit optimum $v_*$ and aligned attainment | Proved, kernel-checked | `result`, with `vStar` and `optMeas`, covers all stable pumps and thermal occupations |
| At $r=0$, every physical stationary covariance is $\nu I$ | Proved, kernel-checked | `zero_pump_covariance`, used by `dimensionless_lower`; physicality and source reduction supply its hypotheses |
| As $r\to1^-$, $z_{m,\rm opt}\to0$ | Proved in prose below | The limiting homodyne measurement is not a finite covariance at $r=1$ and is outside `claim` |
| Zero-temperature optimality of every pure measurement | Open as a separate formal statement | `result` includes $\nu=1$ for the lower bound and an aligned attainer, but does not quantify equality for every pure measurement |
| Multimode or non-passive couplings | Open | No extension of the two-dimensional passive-coupling proof is claimed |
| Transient optimum | Open | `steadyEq` is stationary; no finite-time optimum theorem is claimed |
| Numerical check | Computed | The pinned experiment and exact tested scope in Evidence; exit 0, `ALL_OK` |
| Literature status, including Liu–Chen | Literature reading; completeness `ASSUMED-UNVERIFIED` | The bounded screen above reports no OPO optimum theorem; SciPost concerns arbitrary two-qubit states |

Write $d=\det S=v^2$, $h=S_{01}$, $T=(1+r)S_{00}+(1-r)S_{11}$ and $\varepsilon=(\det M-1)\det R$. The kernel-checked determinant identity is

$$F_+(v)F_-(v)=(\nu^2-1)r^2h^2+\nu(d-1)(T-2cv)+\varepsilon,$$

where $F_+(v)=v^2-(\nu+1)cv+\nu$ and $F_-(v)=v^2-(\nu-1)cv-\nu$. Each summand on the right is nonnegative. The positive-semidefinite factor $W$ gives $\nu T\le2d$, while the trace estimate gives $2cv\le T$, hence $v\ge\nu c$. For $r>0$,

$$F_+(v)=(v-\nu c)^2+(\nu-1)c(v-\nu c)+\nu r^2>0.$$

This excludes the wrong quadratic branch without a homotopy or a continuity argument.

For the equality characterization in prose, assume $r>0$ and $\nu>1$. At $v=v_*$, $F_-(v)=0$, so the three nonnegative defect terms vanish. Since $F_-(1)=-(\nu-1)(1+c)<0$, its positive root has $v_*>1$; thus the correlation and imbalance coefficients are strictly positive. Consequently $h=0$ and $T=2cv$, which together with $d=v^2$ give

$$S=\operatorname{diag}\left(\frac{cv}{1+r},\frac{cv}{1-r}\right),\qquad R=(\nu-cv)I.$$

The positive-root comparison at $\nu$ gives $v_*\le\nu$, because $F_-(\nu)=\nu(\nu-1)(1-c)\ge0$. Hence $\nu-cv>0$, and $\varepsilon=0$ implies $\det M=1$. Both entries of $V$ are nonzero: the first is negative since $cv/(1+r)<\nu$, and the second is positive since $v\ge\nu c$ implies $cv/(1-r)\ge\nu(1+r)>\nu$. Therefore $Q=V^{-1}RV^{-1}$ is diagonal. Substituting its two diagonal entries in $M=Q^{-1}-\nu I$ and using $v^2=(\nu-1)cv+\nu$ gives $M=M_*$. This proves the aligned, balanced, pure equality description in the nondegenerate regime; it is a prose consequence, not a new kernel-checked equality theorem. The degenerate cases $r=0$ and $\nu=1$ do not support an unconditional uniqueness assertion.

For the homodyne limit in prose, $z_{m,\rm opt}=(1-r)/(1+r)$ has numerator tending to zero and denominator tending to two as $r\to1^-$. Its limit is zero. The reciprocal variance diverges, so this is a limiting measurement, not an additional finite-covariance attainer.

The source's conclusions that use the steady-state covariance optimum can use the universal bound and aligned attainer within the same OPO assumptions. The theorem does not add a physical convergence assertion, measurement uniqueness at degenerate parameters, a multimode result or a transient optimum.

## ASSUMED-UNVERIFIED

Literature completeness remains `ASSUMED-UNVERIFIED`; the cited screen and SciPost reading do not exclude every publication. The literature readings attributed above are orchestrator- or seat-reported. The source's ergotropy and monitoring interpretation is external to the formal covariance theorem. The two public escape audits are unfinished under #16704, and no `declared_validated` registration is asserted.
