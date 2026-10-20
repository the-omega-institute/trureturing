---
slug: fu-luo-decoherence-convexity
bibkey: fuluo2021decoherence
doi: 10.3390/e23121594
url: https://www.mdpi.com/1099-4300/23/12/1594
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.result
---

# Fu–Luo decoherence convexity is false

## Problem

S. Fu and S. Luo, *Quantifying Decoherence via Increases in Classicality*, Entropy 23 (2021), 1594, Section 3, after Proposition 3:

> We conjecture that D(ρ_S|Π, U) is convex in ρ. It seems that a proof may require some deep mathematics.

The [source note](../Library/Entropy/fuluo2021decoherence.md) identifies DOI 10.3390/e23121594. Issue [#19026](https://github.com/the-omega-institute/trureturing/issues/19026) fixes the universally quantified reading and the literal conventions.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Eq. (17), $J(\rho,\Pi)=1+\sum_i\langle i|\sqrt\rho|i\rangle^2$ | `J` | Standard pointer basis of `Fin d`; real part of the squared diagonal entry. Positive matrix square roots have real diagonal entries. |
| Eq. (18), $H_E=\bigotimes_i H_{E_i}$, each $U_{E_i}$ acts only on its own part | `EnvIdx`, `liftE` | Arbitrary local dimensions `k`; equality on every other coordinate. |
| Product initial state $\rho_E=\bigotimes_i\rho_{E_i}$ | `rhoE` | Each factor is the reused `DensityState`. |
| Eq. (21), $\omega_{ij}=\operatorname{tr}(U_{E_i}\rho_EU_{E_j}^\dagger)$ | `omega` | Exact lifted-operator trace. |
| Eq. (22), $\rho'_S=\rho_S\circ\Omega$ | `finalState` | Entrywise multiplication. |
| Eq. (27), $D=J(\rho'_S,\Pi)-J(\rho_S,\Pi)$ | `D` | Same environment and detector family for each input. |
| Convexity in $\rho$ | `claim` | Every dimension, product environment, local-unitary family, two density states and $0\le t\le1$; Jensen inequality. |
| Refutation | `result` | Negation of that complete claim. |

There is no extra physical hypothesis. `CStarMatrix.ofMatrix.symm` is the coordinate equivalence from the reused density-state representation to matrices. The conventions in `claim` are the literal preregistered expressions; `DensityState` and `ProbeComponentRigidity.probe` are reused in the proof construction.

## Motivation

The conjecture asks whether the increase in the square-root classicality functional behaves convexly under mixing. A partial-decoherence example distinguishes it from complete dephasing and from the quadratic quantifier $F$.

## Gap

The literature screen recorded in #19026 found no settlement among the source, Qureshi–Qureshi (arXiv:2512.19617v4), Zhang–Wu–Fei (arXiv:2312.12800v1), Fu–Luo–Zhang (Front. Phys. 2022; arXiv:2604.20118v1), Fu–Luo (2019), and Lieb's concavity results. The Crossref record has six citing works and no recorded correction or update; Europe PMC reported zero PMC citations. These are bounded source readings, not an exhaustive priority claim.

The full texts of Luo–Sun, DOI 10.1007/s41884-023-00096-y, and Wu–Zhang–Fei, DOI 10.1007/s11128-024-04637-x, remain unread beyond previews. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Use four system coordinates and four qubit environments, each initially $|0\rangle\langle0|$, with local detector matrices $(X,X,Z,Z)$. The overlap matrix is

$$\Omega=\begin{pmatrix}1&0&0&0\\0&1&0&0\\0&0&1&1\\0&0&1&1\end{pmatrix}.$$

Put $v_0=(1,1,\sqrt3,\sqrt3)^T$, $v_1=(1,-1,\sqrt3,-\sqrt3)^T$ and $\rho_b=v_bv_b^\dagger/8$. Their midpoint is $M=(\rho_0+\rho_1)/2$. Positive square-root certificates give

$$D(\rho_0)=D(\rho_1)=\frac5{16},\qquad D(M)=\frac38,$$

so the Jensen gap is $1/16>0$. The module's sole public theorem `result` refutes `claim`; the matrix and square-root evaluations are consumed private helpers. Each theorem is `bind-only`: finite cases, applications of existing results and normalization. The admission basis is `open-problem-resolution (#19026; Refuted)` and the computational utility is a certified refuting instance. No atom or cover is involved.

## Falsifier

A fidelity failure would be an environment lift that changes other coordinates, a non-product environment, nonunitary detectors, non-density inputs, or using a different quantifier. The public definitions retain the source's local lifts, product state, overlap trace, Hadamard final state and $J$ difference; the proof constructs the unitary and density certificates. If the exhibited midpoint satisfied the conjectured Jensen inequality, the refutation would fail.

## Evidence

Kernel evidence: `D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.result : ¬ claim`. Every public declaration's axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. There is one public theorem and no published owner declaration.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment: [Fu–Luo numerical and exact checks](https://github.com/the-omega-institute/trureturing-experiments/tree/eeed8ecf26ac69c7fb6632b104f8e8f5187943a7/docs/reports/fu-luo-2021-decoherence-convexity-refutation). Command: `python3 check.py` in that directory, exit 0 (`RESULT PASS 0`); script SHA-256 `70c69c3e11d14e0bf6ad278d557d2ee9d8ebaaeffe67489e0700b76ddbadc1ad`. The pinned script checks the literal controlled unitary and partial traces exactly with SymPy for $d=4$, and the finite numerical scopes below with NumPy.

## Triage

Tier 1, settlement kind `small-case`; the universal 2021 conjecture is **Refuted**.

### What the settlement shows

| Item | Evidence kind | Conclusion and boundary |
| --- | --- | --- |
| Universal convexity | Kernel-checked: `result` | A $d=4$ instance contradicts convexity. The exact values and positive square-root certificates are private steps in its proof. |
| Even-dimensional family | Computed: pinned experiment | At $p=1/4$, $m=2,3,4$ ($d=4,6,8$), degenerate-detector gaps are $0.062500$, $0.083333$, $0.093750$, agreeing to tolerance $10^{-6}$ with $(1-1/m)p(1-2p)$. The uniform formula for all $m\ge2$ and $0<p<1/2$ is open as a formalization; no general Lean theorem is delivered. |
| Full-rank and interior-overlap robustness | Computed: pinned experiment | At $p=1/4$, $d=4,6,8$, $\varepsilon=a=1-b=2^{-20}/d$, gaps are $0.062154$, $0.083004$, $0.093456$, each above $13/256$. A uniform quantitative perturbation theorem is open. |
| Moderate perturbation | Computed: pinned experiment | At $p=1/4$, $d=4,6,8$, $\varepsilon=0.01$, overlaps $(a,b)=(0.1,0.9)$, gaps are $-0.141472$, $-0.170989$, $-0.178687$. These instances do not violate convexity. |
| Dimensions two and three | Open; finite search computed by pinned experiment | Seed `20261019`, 20,000 random instances per dimension, found no positive Jensen gap. This does not prove convexity in either dimension. |
| Odd dimensions | Open | No uniform odd-dimensional statement is proved here. |
| General family proof | Open | A separate theorem requires a real consumer or settlement goal. |
| Quadratic functional $F$ | Literature reading: source Eq. (31), Proposition 4 | It is a different functional; its convexity is unaffected by this refutation. |

**Mechanism (explanation).** The overlap matrix preserves the lower two-coordinate coherence block while suppressing other off-diagonal entries. Mixing changes the square-root diagonal sums differently before and after that partial dephasing. A difference of concave classicality functionals need not be convex; the displayed instance supplies the strict violation.

**Nearest surviving statement (literature consequence, not a new Lean theorem).** Under complete dephasing the output is diagonal, so its square-root diagonal-square sum is the trace, equal to one. Thus $D=1-\sum_i\langle i|\sqrt\rho|i\rangle^2$; the concavity statement for $J$ in the source yields convexity for that complete-dephasing restriction. The source's Proposition 4 on $F$ remains outside the refuted conjecture, and the source's other proved propositions are not refuted by this instance.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are `ASSUMED-UNVERIFIED`, including the two unread citing full texts named above. Numerical family and robustness checks have exactly the finite scopes in Triage. Uniform family and perturbation theorems, low-dimensional convexity, and odd-dimensional classifications remain open. The complete-dephasing explanation is not delivered as a Lean theorem.
