---
slug: hanotel-loubenets-2025-high-spin-chsh-nonviolation
bibkey: hanotelloubenets2025chshspinone
doi: 10.1088/1402-4896/adcc66
url: https://arxiv.org/abs/2503.05172v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result
---

# Linear spin measurements never violate CHSH for any spin $s\ge1$

## Problem

L. Hanotel and E. R. Loubenets, *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*, Phys. Scr. 100, 055115 (2025), arXiv:2503.05172v2, Introduction, `Final_Revision_Hanotel_Loubenets.tex`, line 201:

> However, up to the moment the problem whether or not the CHSH inequality is violated under Alice and Bob high spin $s\geq1$ measurements is still open -- though specifically this Bell inequality has been used for proving \cite{1, Lou.Kuz.Han:24}  nonlocality of every pure nonseparable two-qudit state.

The same source's Conjecture section, lines 913–914, states:

> Under local Alice and Bob spin-$1$ measurements in an arbitrary nonseparable pure two-qutrit state, the
> CHSH inequality is not violated.

For spin $s$, the measurements are the linear projections $S_u=u\cdot S$ for unit $u\in\mathbb R^3$. The companion paper, E. R. Loubenets and L. Hanotel, *High-spin measurements in an arbitrary two-qudit state*, J. Phys. A: Math. Theor. 58, 265304 (2025), arXiv:2412.03470v2, `Revision_Loubenets_Hanotel.tex`, lines 210–237 and 253–261, specifies the spin matrices and the CHSH operator
$\mathcal B=S_a\otimes S_b+S_a\otimes S_d+S_c\otimes S_b-S_c\otimes S_d$.
Its lines 348–363 give the local-hidden-variable bound $2s^2$.

Issue [#24190](https://github.com/the-omega-institute/trureturing/issues/24190) fixes the reading: for every integer $n=2s\ge2$, every positive semidefinite trace-one complex matrix $\rho$ on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$, and every four unit real directions $a,c,b,d$,
$|\operatorname{tr}(\rho\mathcal B)|\le n^2/2=2s^2$.
This is proved, including integer and half-integer spins $s\ge1$ and both pure and mixed states.

The source definitions and bibliographic locators are also recorded in [the literature note](../Library/Observer/hanotelloubenets2025chshspinone.md).

## Motivation

The question separates entanglement from the correlations accessible through linear spin projections. A uniform bound for every density matrix settles the high-spin question without restricting the state to the special families considered in the source. It also supplies the nonviolation assertion on which the source's Conjecture section bases its conclusions for all pure and mixed two-qutrit states.

## Gap

The bounded literature check recorded in #24190 distinguishes these results:

- Hanotel and Loubenets (2025), arXiv:2503.05172v2, state the high-spin question and the spin-1 conjecture at the quoted locations.
- Loubenets and Hanotel (2025), arXiv:2412.03470v2, Theorem 1, give the maximum through the two largest singular values of the spin correlation matrix; that theorem does not supply the uniform bound $2s^2$ for $s\ge1$.
- H. Cha and J. Lee (2026), *CHSH inequality always holds in bipartite qutrits with spin-1 observables*, arXiv:2603.10296v2, `apssampv1.tex`, theorem at lines 263–269 and Discussion at lines 564–566, settle the spin-1 case for all two-qutrit states. This special case is already literature-attested.
- R. P. Sandhir and V. Ravishankar (2016), *Weak Classicality in Coupled N-Level Quantum Systems*, arXiv:1602.04905, `mainweakclass.tex`, Linear correlations subsection, lines 198–211, establish nonviolation of linear-spin CHSH correlations for the spin singlet, rather than every density matrix.

Issue #24190 also records web, arXiv, citation-index and repository searches. No general-state settlement for $s\ge3/2$ was located in the searched scope.

`not-found-in-searched-scope`.

## Route

Write $D_n$ for the module's `dicke` matrix and $P_r(u)$ for `slotPauli n r u`; the qubit basis is indexed by subsets of $\mathrm{Fin}\,n$.

1. **Isometry.** For every natural $n$, `dicke_isometry` proves $D_n^\dagger D_n=I$, where $D_n|k\rangle=\binom nk^{-1/2}\sum_{|x|=k}|x\rangle$ for $0\le k\le n$.
2. **Slot observables.** For every natural $n$, slot $r\in\mathrm{Fin}\,n$ and real direction $u$, `slot_hermitian` proves that $P_r(u)$ is Hermitian. With the additional hypothesis `unit u`, `slot_square` proves $P_r(u)^2=I$. For slots $r,t\in\mathrm{Fin}\,n$ with $r\ne t$ and arbitrary real directions $u,v$, `slots_commute` proves that $P_r(u)$ and $P_t(v)$ commute.
3. **Compression.** For every natural $n$, slot $r\in\mathrm{Fin}\,n$ and real direction $u$, `slot_compression` proves $D_n^\dagger P_r(u)D_n=(2/n)S_u$; the existence of $r$ entails $n>0$, and no unit-direction hypothesis is needed here. Its raising part uses `raising_coefficient` for natural $n,k$ with $k<n$, which applies the published `TemporalHardySpinAttainment.ladder_pair` under exactly that hypothesis. The diagonal part is `z_compression`, for every $n$ and $r\in\mathrm{Fin}\,n$.
4. **CHSH dilation.** For every $n\ge2$ and arbitrary real $a,c,b,d$, `chsh_dilation` proves $\mathcal B=(n/2)^2V_n^\dagger L V_n$, where $V_n=D_n\otimes D_n$ and $L$ is `liftedOperator` using slots $0$ and $1$ for each party's two settings. For every natural $n$, `dilation_isometry` proves $V_n^\dagger V_n=I$.
5. **Square identity.** For $n\ge2$ and arbitrary real $a,c,b,d$, `lifted_hermitian` proves that $L$ is Hermitian. Under the additional four hypotheses `unit a`, `unit c`, `unit b`, `unit d`, `lifted_square` proves $L^2=4I$. The reused `LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes` requires finite index types with decidable equality, four Hermitian involutions, and commutation of at least one local pair; the slot lemmas supply these hypotheses on the finite subset index types.
6. **Density expectation.** For every natural $n$ and every positive semidefinite $\rho$ with $\operatorname{tr}\rho=1$, `dilated_density` proves that $\tau=V_n\rho V_n^\dagger$ is positive semidefinite with trace one. For any finite index type with decidable equality, positive semidefinite trace-one $\tau$, and Hermitian $L$ with $L^2=4I$, `density_involution_bound` gives $|\operatorname{tr}(\tau L)|\le2$. It bounds $\|L\|$ by $2$ and directly applies the published `GeometricDiscordMutualCorrelationBound.density_expectation_bound`, whose hypotheses are precisely positivity and trace one for the density matrix, with an arbitrary complex matrix as observable. Finally, for $n\ge2$, positive semidefinite trace-one $\rho$ and four unit directions, `expectation_bound` uses trace cyclicity and the dilation identity to obtain $(n/2)^2\cdot2=n^2/2$; `result` applies it.

## Falsifier

A bound for different observables or a differently normalized CHSH expression would not settle this question. The correspondence is entrywise: put $k=m-1$ and $n=2s$ in the companion source's matrices at lines 225–231. The frozen definitions `PrecessionSpinOneSeparableBound.Jx`, `Jy`, `Jz` have
$(J_x)_{k,k+1}=\sqrt{(k+1)(n-k)}/2$,
$(J_y)_{k,k+1}=\sqrt{(k+1)(n-k)}/(2i)$, and
$(J_z)_{kk}=n/2-k$,
with $0\le k<n$ in the off-diagonal formulas and $0\le k\le n$ on the diagonal; the lower off-diagonal entries are the complex conjugates and all other entries vanish. `TemporalHardySpinAttainment.spinComponent` is exactly $u_0J_x+u_1J_y+u_2J_z$.

The module's `unit` means $u_0^2+u_1^2+u_2^2=1$, and `chshOperator` has the source's four signs and tensor factors. The conclusion is the complex modulus of the trace, for every positive semidefinite trace-one matrix in the stated equal local dimensions. It imposes no separability or purity restriction. It addresses linear spin projections and CHSH; nonlinear functions of spin, other Bell inequalities and spin $1/2$ are outside `claim`.

## Evidence

The canonical source is `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean.json`.

Declaration statements:

- `result`: `sha256:cc5f6a00713c499dc27ac86cf567fad19c19c8377ea27eaf2773ab56e16a07c3`;
- `claim`: `sha256:897fbf8ae64b122696449eaae2726fca459f09afff34300f5e6e93f8435998cc`.

## Triage

Tier 1 open problem stated in a 2025 paper, preregistered in issue #24190 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every integer $n\ge2$, every positive semidefinite trace-one complex matrix $\rho$ on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$, and every four real directions $a,c,b,d$ satisfying $u_0^2+u_1^2+u_2^2=1$ for each direction $u$, the modulus of the trace of $\rho$ times `chshOperator n a c b d` is at most $n^2/2$.

**Computed, not formalized**. None.

**Argued, not formalized**.

- *Mechanism.* For $n\ge2$, unit local directions and distinct slots $0,1\in\mathrm{Fin}\,n$, `slot_compression`, `slot_hermitian`, `slot_square` and `slots_commute` represent the normalized linear spin components by compressions of commuting Hermitian involutions. Slot-independent compression lets the two settings use different qubits. This controls the first moments entering the four CHSH correlations; it does not identify the full multivalued outcome distributions with those of a commuting measurement model.
- *Sharpness.* For every integer $n\ge2$, choose all four directions along $z$ and the pure product state $|0\rangle\otimes|0\rangle$. Then $\mathcal B=2J_z\otimes J_z$ and $J_z|0\rangle=(n/2)|0\rangle$, so its expectation is exactly $n^2/2$. Thus the uniform constant cannot be reduced. This attainment assertion is not part of `result`.
- *Neighbouring extension.* Let $n\ge2$, $s=n/2$, and let $\rho$ be a positive semidefinite trace-one matrix on $\mathbb C^{n+1}\otimes\mathbb C^q$ with $q\ge1$. Give Alice two unit spin directions and Bob two Hermitian observables $B_0,B_1$ with operator norms at most $t\ge0$. Dilating Alice alone, `dicke_isometry` and `slot_compression` supply the isometry and the scale $s$; `slot_hermitian`, `slot_square` and `slots_commute` apply to her unit directions on distinct slots. Her lifted observables $\alpha,\gamma$ are commuting Hermitian involutions. On a joint eigenspace with eigenvalues $\varepsilon,\eta\in\{\pm1\}$, the lifted CHSH matrix is $(\varepsilon+\eta)B_0+(\varepsilon-\eta)B_1$, one of $\pm2B_0,\pm2B_1$, hence has norm at most $2t$. Compression and the density expectation inequality give the bound $2st$. This argument includes unequal spins whenever at least one spin is at least one; the asymmetric statement is not formalized here.
- *The excluded qubit case.* For $n=1$, take $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$, $a=z$, $c=x$, $b=(z+x)/\sqrt2$, $d=(z-x)/\sqrt2$, and $S_u=\sigma_u/2$. The Bell operator is $\sqrt2(\sigma_z\otimes\sigma_z+\sigma_x\otimes\sigma_x)/4$; both tensor products have expectation one, giving $\sqrt2/2>1/2$. The dilation route cannot assign two distinct slots at $n=1$.
- *Effect on the source.* For a fixed density matrix the fourfold unit sphere is nonempty and compact, and the trace expression is continuous, so its maximum exists. The universal bound therefore gives $\Upsilon_{chsh}^{(\mathrm{spin}\text{-}s)}\le2s^2$ and the source's normalized parameter $\gamma_s\le1$ for $s\ge1$. At $n=2$ this supplies the nonseparable pure-state conjecture and the all-pure and mixed-state nonviolation conclusions in the source's Conjecture section, lines 918–943, without a conjectural premise. The module includes mixed density matrices directly; it does not formalize the source's singular-value formula, concurrence comparisons or state-dependent optimized values. The distinct question in the Introduction, line 197, of an explicit maximum over all traceless qudit observables is not settled by this bound for linear spin projections.

## ASSUMED-UNVERIFIED

The literature check is bounded and establishes neither exhaustive worldwide novelty nor priority. The source passages identified above were checked directly; the broader web, arXiv and citation-index search results attributed to the orchestrator and search seat in #24190 were not independently reproduced. The source's million-state numerical experiment was not reproduced and is not used as evidence for the universal bound.

The arguments under "What the settlement shows" are not formalized. In particular, sharpness, the asymmetric extension, the spin-$1/2$ witness and the passage to the source's optimized parameter are outside the type of `result`. The source's other analytical and numerical claims, including the singular-value optimization formula and concurrence comparisons, have not been independently verified as mathematical results here. Bell nonlocality under nonlinear spin observables, other Bell inequalities, and general traceless qudit observables is not decided by this settlement.
