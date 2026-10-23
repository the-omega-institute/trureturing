---
slug: sud-marshall-wang-rieffel-wudarski-2022-maten-worst-case-fidelity
bibkey: sudmarshallwangrieffelwudarski2022dual
doi: 10.1103/PhysRevA.106.012606
url: https://arxiv.org/abs/2112.04414v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.result
---

# The sharp worst-case MATEN process fidelity is $4^{-N}$ for $N\ge2$

## Problem

J. Sud, J. Marshall, Z. Wang, E. Rieffel and F. A. Wudarski, *Dual-map framework for noise characterization of quantum computers*, arXiv:2112.04414v1 (2021); Phys. Rev. A 106, 012606 (2022), Section IV, “Local vs Non-Local Channels”, state:

> We conjecture that the effective channel with the maximally entangled $\chi$ matrix is the worst case scenario for the proposed MATEN protocol.

> However, this conjecture requires more rigorous treatment, which we leave as an open problem.

These sentences occur in `main.tex`, lines 289 and 290, respectively, in the downloaded v1 source (709 lines; MD5 `b2275e7db7e3a63cc4c871c172f7943a`). The source specifies $\chi=|\Psi\rangle\langle\Psi|$ with $|\Psi\rangle=\tfrac12\sum_{i=0}^3|ii\ldots i\rangle$ on $N$ four-dimensional process factors (lines 286–289), and evaluates $F(\chi,\chi_{\mathrm{MA}})=4^{-N}$ (lines 292–296). Its MATEN definition is at lines 226–232. See also [the literature note](../Library/QuantumContext/sudmarshallwangrieffelwudarski2022dual.md).

Issue [#20689](https://github.com/the-omega-institute/trureturing/issues/20689) fixes the settlement as a universal fidelity lower bound and attainment by cyclic wire permutations. The source's particular GHZ witness and its trace-preservation assertion require the qualification in Triage.

Write $a\in\{0,1,2,3\}^N$ for a Pauli string and $P_a=\bigotimes_k\sigma_{a_k}$, with $\sigma_0=I$, $\sigma_1=X$, $\sigma_2=Y$ and $\sigma_3=Z$, without Hilbert–Schmidt normalization. The formal definitions are:

- `IsProcessCPTP` means $\chi\succeq0$ and $\sum_{a,b}\chi_{ab}P_bP_a=I$. This is the process representation of $\mathcal E_\chi(\rho)=\sum_{a,b}\chi_{ab}P_a\rho P_b$, matching the source's CP and TP conditions at lines 93–100.
- `marginal` is the single-site partial trace: $(\chi_k)_{ij}=\sum_{y:y_k=i}\chi_{y,y[k\leftarrow j]}$. `productMap` forms $\chi_{\mathrm{MA}}=\bigotimes_k\chi_k$, entrywise $(\chi_{\mathrm{MA}})_{ab}=\prod_k(\chi_k)_{a_kb_k}$.
- The fidelity used is squared Uhlmann fidelity, $F(\rho,\sigma)=(\operatorname{Re}\operatorname{tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho})^2$, exactly `sqFidelity`. This convention agrees with the source's projector calculation and distinguishes squared fidelity from root fidelity.
- Put $U_N=(\mathtt{qubitPermutation}(\mathtt{finRotate}\,N))^{\mathsf T}$. Here the untransposed permutation matrix has entries $1$ when $y=x\circ\mathtt{finRotate}\,N$ and $0$ otherwise. `shiftCoeff` is $\psi_N(a)=2^{-N}\operatorname{tr}(P_aU_N)$, and `rankOneDensity` gives $\chi_N=\psi_N\psi_N^\dagger$, with entries $\psi_N(a)\overline{\psi_N(b)}$.

## Motivation

MATEN retains each single-qubit process marginal and discards correlations between different process coordinates. A worst-case fidelity bound determines how much global process information this approximation can lose even when the marginals are known exactly. The attaining family must satisfy trace preservation as well as positivity: an arbitrary density matrix on the process coordinates need not describe a channel.

## Gap

The bounded literature check recorded in #20689 reports:

- the orchestrator's arXiv check lists only v1, which contains the conjecture;
- the orchestrator's OpenAlex lookup for W4226541574 lists one citing work, *Assessing and advancing the potential of quantum computing: A NASA case study* (2024), DOI 10.1016/j.future.2024.06.012; the GPT Pro search seat reports that Section 5.4 cites the framework without settling the conjecture;
- the orchestrator's web searches for the MATEN worst case and fidelity against the product of marginals, Zenodo query for “marginal approximation” and “effective noise”, and Naixu-Guo/quantum-open-problems issue and code searches for MATEN and 2112.04414 locate no settlement; the search seat reports no MathDB page;
- the orchestrator's repository search in Problems, Library and issues locates no settlement.

`not-found-in-searched-scope`. The preregistration identifies the entropy and fidelity inequalities as standard ingredients; the settlement concerns their application to the published question and a valid attaining channel family.

## Route

1. **Classical overlap.** For a probability distribution $p$ on the Pauli strings, let $q_k(j)=\sum_{x:x_k=j}p(x)$. Weighted AM–GM with weights $q_k(j)$ and values $q_k(j)^{-1}$ gives $\prod_jq_k(j)^{q_k(j)}\ge1/4$. Zero weights contribute zero to the arithmetic sum and one to the geometric product. A second weighted AM–GM inequality, with weights $p(x)$ and values $\prod_kq_k(x_k)$, gives $\sum_xp(x)\prod_kq_k(x_k)\ge\prod_{k,j}q_k(j)^{q_k(j)}\ge4^{-N}$.
2. **Quantum overlap.** Trace the TP identity and use $\operatorname{tr}(P_bP_a)=2^N\delta_{ab}$ to obtain $\operatorname{tr}\chi=1$. Diagonalize each positive marginal and conjugate $\chi$ by the product of these local unitaries. Its diagonal is a probability distribution whose single-site marginals are precisely the marginal eigenvalues. The classical overlap is therefore $\operatorname{Re}\operatorname{tr}(\chi\chi_{\mathrm{MA}})$.
3. **Fidelity.** For positive $\rho,\sigma$, put $S=\sqrt{\sqrt\rho\,\sigma\sqrt\rho}$. Positivity gives $\operatorname{Re}\operatorname{tr}(S^2)\le(\operatorname{Re}\operatorname{tr}S)^2$. Cyclicity of trace identifies the left side with $\operatorname{Re}\operatorname{tr}(\rho\sigma)$, giving the fidelity lower bound.
4. **Attainment.** Pauli expansion reconstructs $U_N$ from `shiftCoeff`; its unitarity supplies the TP identity for $\chi_N$. In each marginal contraction, Pauli completeness identifies both wire indices at every discarded site. For $N\ge2$ the predecessor of the retained site is distinct from it, so these constraints identify all wire indices, and the remaining Pauli orthogonality gives $\chi_{N,k}=I_4/4$. The product is $4^{-N}I$; trace one and the outer-product form make $\chi_N$ a projector, so substituting into `sqFidelity` gives $4^{-N}$.

## Falsifier

A counterexample to the universal conjunct would be an $N\ge1$ matrix satisfying exactly `IsProcessCPTP` with squared fidelity below $4^{-N}$. A failure of the registered attaining family would be an $N\ge2$ for which its Pauli expansion, TP identity, marginal identity or fidelity equality does not hold.

Source fidelity also requires the unnormalized Pauli convention, the ordered product $P_bP_a$ in the TP identity, partial traces over four-dimensional process coordinates, and squared fidelity. The settlement does not assert that the source's GHZ projector is CPTP for every $N$. It establishes the registered bound and cyclic-shift attainment. No infimum or supremum definition is used: the claim supplies both the lower bound and an explicit admissible matrix attaining it.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.lean` (681 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity.lean.json`, statement `sha256:fe11e01ca6180e4e80035a4777d14c525b6b38feec6c27c3405044f01e6168ac`.

Declaration statements:

- `result`: `sha256:5dae0249a7976cb892294549b1c8a44280c2c512878c4fbf02c487b67d96ac67`;
- `claim`: `sha256:de483b92cb0a3894c6a50d61d48e6c4e88520a96f0b259ca97e8f63093bd23d2`.

## Triage

Tier 1 conjecture of a 2021 preprint published in 2022, preregistered in issue #20689 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $N\ge1$ and every matrix $\chi$ satisfying `IsProcessCPTP`, $F(\chi,\bigotimes_k\chi_k)\ge4^{-N}$. For every $N\ge2$, the coefficients $\psi_N=\mathtt{shiftCoeff}\,N$ satisfy $\sum_a\psi_N(a)P_a=U_N$; the matrix $\chi_N=\psi_N\psi_N^\dagger$ satisfies `IsProcessCPTP`; every marginal is $I_4/4$; and $F(\chi_N,\bigotimes_k\chi_{N,k})=4^{-N}$. These are the two conjuncts of `claim`, including all four assertions about the attaining family.

**Computed, not formalized.** None; the GHZ trace-preservation criterion below is argued for every $N$.

**Argued, not formalized.**

- *Decisive mechanism and sharpness.* The lower bound comes from normalization and the local dimension through classical overlap, rather than an entanglement ordering. For $N\ge2$, its combination with the explicit cyclic-shift equality means the minimum over CPTP process matrices is $4^{-N}$; no larger uniform lower bound is possible. No characterization of all minimizers is supplied.
- *Scope beyond channels.* For any density matrix on a finite product with local dimensions $d_k\ge1$, the same diagonalization gives a classical distribution $p$. Applying the two weighted AM–GM steps with $d_k$ terms gives $\sum_xp(x)\prod_kq_k(x_k)\ge\prod_kd_k^{-1}$. The positive-matrix trace inequality then gives $F(\rho,\bigotimes_k\rho_k)\ge\prod_kd_k^{-1}$. TP is used in the channel proof only to obtain trace one. This extension is a mathematical argument, not an additional conclusion of `result`; channel attainment in arbitrary dimensions is not established here.
- *The one-qubit boundary.* With one process coordinate the partial trace retains the whole matrix, so $\chi_{\mathrm{MA}}=\chi$. For a density matrix, $\sqrt{\sqrt\chi\,\chi\sqrt\chi}=\chi$, hence $F(\chi,\chi)=1$. Thus the registered $1/4$ bound at $N=1$ is not sharp; the attainment conjunct explicitly starts at $N=2$.
- *The source's GHZ restriction.* Put $A=X^{\otimes N}$, $B=Y^{\otimes N}$ and $C=Z^{\otimes N}$. Their squares are $I$, and the three pairwise anticommutators are $2\operatorname{Re}(i^N)$ times the remaining operator. Expanding $K_N^\dagger K_N$ therefore gives $I+\tfrac{1+\operatorname{Re}(i^N)}2(A+B+C)$. For $N\ge1$, Pauli trace orthogonality makes $A+B+C$ nonzero. TP consequently holds exactly when $N\equiv2\pmod4$. The source's assertion at line 290, “Note that maximally entangled $\chi$ is a completely valid choice, since $\chi\ge0$ and the map associated with it is trace preserving.”, needs this restriction for its specified GHZ state. Cyclic shifts provide the attaining process in the formal claim for every $N\ge2$.
- *Effect on the paper and neighbouring questions.* Section IV's use of $4^{-N}$ as a global worst-case fidelity for $N\ge2$ is justified by the registered settlement with a valid attaining family. The source's formula for its GHZ projector remains a density-matrix calculation for $N\ge2$; interpreting that particular projector as a channel requires the TP restriction above. The numerical studies of random and Pauli channels at lines 298–313, the claimed practical accuracy near the identity at lines 296 and 313, and the hardware observations are separate statements. A sharp improved bound at fixed $\chi_{00}$, a description of all equality cases, and the symmetry-related identification question at line 278 are not settled by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check in #20689 does not establish exhaustive worldwide novelty or priority. Its arXiv version listing, OpenAlex citation count, web, Zenodo and quantum-open-problems searches, MathDB report, and the citing paper's Section 5.4 reading are attributed reports and were not independently reproduced for this dossier. The source reading reproduced here is the v1 `main.tex` with the MD5 above; the journal text and the 2024 citing paper were not read here.

Everything labelled “Computed, not formalized” or “Argued, not formalized” is outside the statement of `result`, including the GHZ TP criterion, the one-qubit sharp value, and the extension to arbitrary local dimensions. The paper's simulations, numerical optimization and hardware experiments were not reproduced. The theorem concerns exact process marginals and their squared fidelity; it does not certify finite-sample reconstruction, observable prediction, a bound conditioned on $\chi_{00}$, or a classification of minimizers.
