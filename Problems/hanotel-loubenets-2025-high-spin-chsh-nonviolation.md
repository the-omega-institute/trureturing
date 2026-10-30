---
slug: hanotel-loubenets-2025-high-spin-chsh-nonviolation
bibkey: hanotelloubenets2025chshspinone
doi: 10.1088/1402-4896/adcc66
url: https://arxiv.org/abs/2503.05172v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result
---

# Linear spin measurements never violate CHSH for spin $s\ge1$

## Problem

L. Hanotel and E. R. Loubenets, *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*, Phys. Scr. 100 (2025) 055115, arXiv:2503.05172v2, Introduction, `Final_Revision_Hanotel_Loubenets.tex`, line 201:

> However, up to the moment the problem whether or not the CHSH inequality is violated under Alice and Bob high spin $s\geq1$ measurements is still open -- though specifically this Bell inequality has been used for proving \cite{1, Lou.Kuz.Han:24}  nonlocality of every pure nonseparable two-qudit state.

Section 5, “Conjecture”, lines 913–914, states:

> Under local Alice and Bob spin-$1$ measurements in an arbitrary nonseparable pure two-qutrit state, the
> CHSH inequality is not violated.

The spin observables are specified in E. R. Loubenets and L. Hanotel, *High-spin measurements in an arbitrary two-qudit state*, J. Phys. A: Math. Theor. 58 (2025) 265304, DOI 10.1088/1751-8121/ade4e8, arXiv:2412.03470v2, `Revision_Loubenets_Hanotel.tex`, lines 210–233. They are $S_u=u\cdot S$ for real unit directions $u$, on dimension $2s+1$. Its CHSH operator is given at lines 253–261, and its local-hidden-variable bound $2s^2$ at lines 348–363.

Issue [#24190](https://github.com/the-omega-institute/trureturing/issues/24190) fixes the general reading: for every integer $n\ge2$, put $s=n/2$ and let $\rho$ be any positive semidefinite, trace-one complex matrix on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$. For every four real unit directions $a,c,b,d$, define

$\mathcal B=S_a\otimes S_b+S_a\otimes S_d+S_c\otimes S_b-S_c\otimes S_d$.

The assertion is $|\operatorname{tr}(\rho\mathcal B)|\le n^2/2=2s^2$. This includes every integer and half-integer spin $s\ge1$, with no purity or separability restriction. The module proves this assertion as `result : claim`.

## Motivation

The question distinguishes entanglement from the correlations accessible through physical spin components. A state may be entangled while these restricted observables cannot reveal a CHSH violation. A bound uniform in the state and spin answers the general high-spin question, beyond the two-qutrit conjecture and its sampled or explicitly evaluated families.

## Gap

The bounded literature check recorded in #24190 before any Lean distinguishes the general problem from its known spin-1 case:

- Hanotel and Loubenets (2025), arXiv:2503.05172v2, retain the high-spin question and spin-1 conjecture; Loubenets and Hanotel (2025), arXiv:2412.03470v2, give the spin-correlation formula for the maximum without a general nonviolation theorem.
- H. Cha and J. Lee (2026), *CHSH inequality always holds in bipartite qutrits with spin-1 observables*, arXiv:2603.10296v2, prove nonviolation for every two-qutrit state. Their Theorem, Corollary and Discussion concern spin 1. Thus the spin-1 conclusion already has a literature proof.
- The orchestrator's reading of Sandhir and Ravishankar, arXiv:1602.04905, recorded in #24190, concerns linear spin correlations in singlet states, rather than arbitrary states.
- The orchestrator's web and repository searches, and the search contributor's citation and arXiv searches recorded in #24190, found no settlement covering every spin $s\ge3/2$ and arbitrary states.

For that general range: `not-found-in-searched-scope`.

## Route

All unqualified lemma names below belong to `HighSpinCHSHNonviolation`; the dilation and compression lemmas are private.

1. **Isometric embedding.** For every natural $n$, `dicke_isometry` proves $D_n^\dagger D_n=I$, where $D_n|k\rangle=\binom nk^{-1/2}\sum_{|x|=k}|x\rangle$ and $x$ ranges over subsets of $\mathrm{Fin}\,n$. For every natural $n$, `dilation_isometry` proves the same identity for $V=D_n\otimes D_n$.
2. **Each slot has the same compression.** For every natural $n$, slot $r:\mathrm{Fin}\,n$ and real direction $u:\mathrm{Fin}\,3\to\mathbb R$, `slot_compression` proves $D_n^\dagger\sigma_r(u)D_n=(2/n)S_u$. This lemma does not require $u$ to be unit; the existence of $r$ entails $n>0$. Here $S_u$ is exactly the reused `TemporalHardySpinAttainment.spinComponent n u`.
3. **Distinct slots give the bound's algebra.** For every $n\ge2$ and arbitrary real directions $a,c,b,d$, `chsh_dilation` proves $\mathcal B=(n/2)^2V^\dagger L V$, where $L=\alpha(\beta+\delta)+\gamma(\beta-\delta)$ uses slot 0 for $a,b$ and slot 1 for $c,d$ on their respective parties. For every natural $n$, slot $r$ and real $u$, `slot_hermitian` proves Hermiticity; with the additional hypothesis `unit u`, `slot_square` proves $\sigma_r(u)^2=I$. For slots $r,t:\mathrm{Fin}\,n$ with $r\ne t$ and arbitrary real $u,v$, `slots_commute` proves commutation. For $n\ge2$ and arbitrary four real directions, `lifted_hermitian` proves $L$ Hermitian; with all four directions unit, `lifted_square` proves $L^2=4I$.
4. **Density and expectation.** For every natural $n$ and every positive semidefinite matrix $\rho$ on the two spin spaces with $\operatorname{tr}\rho=1$, `dilated_density` proves that $\tau=V\rho V^\dagger$ is positive semidefinite with trace one. For matrices $\tau,L$ indexed by any finite type with decidable equality, `density_involution_bound` assumes $\tau\succeq0$, $\operatorname{tr}\tau=1$, $L=L^\dagger$ and $L^2=4I$, and proves $|\operatorname{tr}(\tau L)|\le2$. Finally, `expectation_bound`, under $n\ge2$, $\rho\succeq0$, $\operatorname{tr}\rho=1$ and four unit real directions, uses trace cyclicity and the factor $(n/2)^2$ to obtain $|\operatorname{tr}(\rho\mathcal B)|\le n^2/2$.

## Falsifier

The proof would not answer the source if it used different spin matrices, normalization or measurement families. The definitions agree under $k=m-1$ and $n=2s$:

- `Jz n` has diagonal $n/2-k$.
- `Jplus n` has upper adjacent entry $\sqrt{(k+1)(n-k)}$ for $0\le k<n$ and zero elsewhere; `Jx` and `Jy` are respectively $(J_++J_+^\dagger)/2$ and $(J_+-J_+^\dagger)/(2i)$. These match the companion source's matrices, including the sign of $S_2$.
- `spinComponent n u` is $u_0J_x+u_1J_y+u_2J_z$, and `unit u` means $u_0^2+u_1^2+u_2^2=1$.
- `chshOperator` has the source's three plus signs and one minus sign. Its expectation is the modulus of the complex trace $|\operatorname{tr}(\rho\mathcal B)|$, bounded by the unnormalized local bound $2s^2$.

The claim concerns equal local spins and linear spin components. It neither assumes separability nor restricts to selected state families. Spin $1/2$, nonlinear functions or outcome processing of spin, and other Bell inequalities are outside its statement. No supremum or infimum is used in `claim`.

## Evidence

The canonical source is `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean.json`.

Declaration statements:

- `result`: `sha256:cc5f6a00713c499dc27ac86cf567fad19c19c8377ea27eaf2773ab56e16a07c3`;
- `claim`: `sha256:897fbf8ae64b122696449eaae2726fca459f09afff34300f5e6e93f8435998cc`.

## Triage

Tier 1 open problem of a 2025 paper, preregistered in issue #24190 before any Lean. The general high-spin question extends the spin-1 case proved by Cha and Lee (2026), arXiv:2603.10296v2.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge2$, every positive semidefinite, trace-one complex matrix $\rho$ on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$ and all $a,c,b,d\in\mathbb R^3$ satisfying $u_0^2+u_1^2+u_2^2=1$ for each direction $u$, the operator $\mathcal B=S_a\otimes S_b+S_a\otimes S_d+S_c\otimes S_b-S_c\otimes S_d$ satisfies $|\operatorname{tr}(\rho\mathcal B)|\le n^2/2$.

**Computed, not formalized**. None.

**Argued, not formalized.**

- *Decisive mechanism.* For $n\ge2$ and four unit real directions, the identities in `slot_compression` and `chsh_dilation`, with the slot and dimension hypotheses stated in Route, realize the two settings on distinct qubits. The local commutation supplied by `slots_commute` for distinct slots yields the square identity in `lifted_square`. Thus for every positive semidefinite trace-one state the expectation bound comes from a commuting dilation, without a constraint on its entanglement.
- *Sharp uniform constant.* For every $n\ge2$, choose $a=c=b=d=e_z$ and $\rho=|0,0\rangle\langle0,0|$. This rank-one projection is positive semidefinite with trace one; $J_z|0\rangle=(n/2)|0\rangle$ and $\mathcal B=2J_z\otimes J_z$, so its expectation is $n^2/2$. This attains the uniform bound; it does not assert attainment for every fixed state or every fixed choice of directions.
- *Unequal spins.* The same argument extends to natural $n\ge2$, $m\ge1$, a positive semidefinite trace-one state on $\mathbb C^{n+1}\otimes\mathbb C^{m+1}$, and four unit real directions. Use $D_n\otimes D_m$, distinct slots on Alice's side and any slots on Bob's side. `slot_compression` applies separately at $n$ and $m$ because each selected slot exists. All four lifted factors are Hermitian involutions by `slot_hermitian` and `slot_square`; Alice's pair commutes by `slots_commute`. The finite-matrix theorem `LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes` requires these four Hermitian-involution hypotheses and commutation of at least one local pair, so it gives $L^2=4I$ even when Bob has only one slot. By `dicke_isometry` at $n$ and $m$, the tensor map satisfies $V^\dagger V=I$, so $\tau=V\rho V^\dagger$ is positive semidefinite and $\operatorname{tr}\tau=\operatorname{tr}(\rho V^\dagger V)=1$. Each CHSH summand is a tensor product of Hermitian matrices, so $L$ is Hermitian, and `density_involution_bound` applies. Compression and trace cyclicity give $|\operatorname{tr}(\rho\mathcal B)|\le nm/2=2s_As_B$. Swapping the parties covers $n\ge1$, $m\ge2$. This extension is not a declaration of the settlement module.
- *Spin-$1/2$ boundary.* At $n=1$, put $a=e_z$, $c=e_x$, $b=(e_z+e_x)/\sqrt2$ and $d=(e_z-e_x)/\sqrt2$. Since $S_j=\sigma_j/2$, $\mathcal B=(\sqrt2/4)(\sigma_z\otimes\sigma_z+\sigma_x\otimes\sigma_x)$. The singlet $(|01\rangle-|10\rangle)/\sqrt2$ has eigenvalue $-1$ under both tensor factors, giving expectation $-\sqrt2/2$. There are no two distinct slots at $n=1$, and the proposed local bound $1/2$ is exceeded in this configuration.
- *Effect on the source.* For fixed $n\ge2$ and a positive semidefinite trace-one state, the four-direction domain $(S^2)^4$ is nonempty and compact and the absolute trace expectation is continuous. Its maximum therefore exists and is at most $2s^2$, so the source's parameter $\gamma_s$, defined as that maximum divided by $2s^2$, is at most one. At $n=2$, this confirms the all-pure-state and mixed-state conclusions conditional on the conjecture in Section 5, TeX lines 917–943, directly for all density matrices. The source's state-dependent singular-value formula and its calculations relating concurrence to CHSH parameters are separate statements and are not formalized by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The source passages and spin conventions, and the Theorem, Corollary and Discussion of Cha and Lee (2026), arXiv:2603.10296v2, were checked against their TeX; a formal equivalence with an external text is not encoded in Lean. Cha and Lee's proof was not independently formalized. The orchestrator's reading of Sandhir and Ravishankar, arXiv:1602.04905, and the search contributor's Semantic Scholar citation listing and 61-record arXiv search reported in #24190 were not independently reproduced. The source's million-state numerical study was not reproduced and is not used as proof.

The arguments in “What the settlement shows”, including sharpness, unequal spins, the spin-$1/2$ example and the maximum/parameter interpretation, are not additional Lean declarations. The source's explicit state-family formulas, concurrence comparisons and claims about broader observable classes were not independently verified. This settlement asserts no general Bell-locality theorem and supplies no result about nonlinear spin observables or other Bell inequalities.
