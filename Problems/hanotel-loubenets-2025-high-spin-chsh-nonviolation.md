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

The same source, §5, lines 913–914, states the spin-1 conjecture:

> Under local Alice and Bob spin-$1$ measurements in an arbitrary nonseparable pure two-qutrit state, the CHSH inequality is not violated.

The measurement conventions are given by E. R. Loubenets and L. Hanotel, *High-spin measurements in an arbitrary two-qudit state*, J. Phys. A: Math. Theor. 58 (2025) 265304, arXiv:2412.03470v2, `Revision_Loubenets_Hanotel.tex`, lines 210–237, 253–261 and 348–365: $S_u=u\cdot S$ for a real unit vector $u$, and the local-hidden-variable CHSH bound is $2s^2$.

Issue [#24190](https://github.com/the-omega-institute/trureturing/issues/24190) fixes the general reading. For every natural $n\ge2$, put $s=n/2$ and let $\rho$ be any positive semidefinite trace-one complex matrix on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$. For all four real unit directions $a,c,b,d$, define $\mathcal B=S_a\otimes S_b+S_a\otimes S_d+S_c\otimes S_b-S_c\otimes S_d$. The assertion is $|\operatorname{tr}(\rho\mathcal B)|\le n^2/2=2s^2$. It is proved for every integer or half-integer spin $s\ge1$, including pure and mixed states.

The source quotations and conventions are also recorded in [the literature note](../Library/Observer/hanotelloubenets2025chshspinone.md).

## Motivation

Spin-component measurements are a physically restricted family of qudit observables. Settling their CHSH bound separates the ability of these measurements to reveal nonlocality from the presence of entanglement. The general question includes the source's two-qutrit conjecture and asks whether increasing the spin permits a violation.

## Gap

The bounded literature check in #24190 records:

- Hanotel and Loubenets (2025), arXiv:2503.05172v2, retain the high-spin question and spin-1 conjecture.
- Loubenets and Hanotel (2025), arXiv:2412.03470v2, Theorem 1, express the maximal spin-CHSH expectation through two singular values of the spin correlation matrix; that expression alone does not establish nonviolation for all states.
- H. Cha and J. Lee (2026), *CHSH inequality always holds in bipartite qutrits with spin-1 observables*, arXiv:2603.10296v2, prove nonviolation for every two-qutrit density operator. Their theorem and Discussion concern spin 1.
- The reported web, citation and arXiv searches found no general settlement for $s\ge3/2$, and the reported repository search found no matching general theorem.

The three source texts above retain these stated scopes. The broader negative search result is `not-found-in-searched-scope`, not an exhaustive novelty claim.

## Route

Write $D_n$ for `dicke n`, $P_{r,u}$ for `slotPauli n r u`, and $V_n=D_n\otimes D_n$ for `dilation n`.

1. **Isometry.** For every natural $n$, $D_n|k\rangle=\binom nk^{-1/2}\sum_{|x|=k}|x\rangle$, where $x$ ranges over subsets of $\mathrm{Fin}\,n$ and $k\in\mathrm{Fin}(n+1)$. Counting these subsets gives $D_n^\dagger D_n=I$ in `dicke_isometry`; `dilation_isometry` gives $V_n^\dagger V_n=I$ for every natural $n$.
2. **Slot compression.** For every natural $n$, slot $r\in\mathrm{Fin}\,n$, and real direction $u$, `slot_compression` gives $D_n^\dagger P_{r,u}D_n=(2/n)S_u$. The slot hypothesis implies $n>0$; no unit hypothesis is needed for this identity. For these same parameters, `slot_hermitian` gives Hermiticity; if additionally `unit u`, `slot_square` gives $P_{r,u}^2=I$. For slots $r,t\in\mathrm{Fin}\,n$ with $r\ne t$ and any real directions $u,v$, `slots_commute` gives $P_{r,u}P_{t,v}=P_{t,v}P_{r,u}$.
3. **Lifted CHSH operator.** For $n\ge2$ and any four real directions, choose slots 0 and 1 for each party's two settings, and write $L$ for `liftedOperator` at those slots. `chsh_dilation` gives $\mathcal B=(n/2)^2V_n^\dagger L V_n$, and `lifted_hermitian` gives Hermiticity of $L$. If all four directions are unit, `lifted_square` gives $L^2=4I$. It applies `LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes`, whose hypotheses are four Hermitian involutions on finite complex matrix spaces and commutation of at least one local pair; the distinct Alice slots supply that commutation.
4. **Density expectation.** For every natural $n$ and positive semidefinite trace-one $\rho$ of the required dimension, `dilated_density` gives the same two properties for $\tau=V_n\rho V_n^\dagger$. On any finite index type with decidable equality, for positive semidefinite trace-one $\tau$ and Hermitian $L$ satisfying $L^2=4I$, `density_involution_bound` gives $|\operatorname{tr}(\tau L)|\le2$ by matrix Cauchy–Schwarz. For $n\ge2$, such a $\rho$ and four unit directions, trace cyclicity and the scale factor give `expectation_bound`, hence `result : claim`.

## Falsifier

A violation for any natural $n\ge2$, positive semidefinite trace-one $\rho$ and four unit real directions would contradict `claim`. A mismatch between the formal spin matrices and the source would instead invalidate the application to the source question.

The module reuses `spinComponent n u`, namely $u_0J_x+u_1J_y+u_2J_z$, and defines `unit u` by $u_0^2+u_1^2+u_2^2=1$. With source basis index $m=k+1$, the repository's diagonal is $(J_z)_{kk}=n/2-k$; its upper adjacent entries are $(J_x)_{k,k+1}=\sqrt{(k+1)(n-k)}/2$ and $(J_y)_{k,k+1}=\sqrt{(k+1)(n-k)}/(2i)$ for $0\le k<n$, with conjugate lower entries. These match the companion source's matrices at $d=n+1$. The norm in `claim` is the complex modulus of the trace, and the bound concerns each choice of directions directly; it uses no infimum or supremum convention.

The claim excludes spin $1/2$, nonlinear functions or dichotomic replacements of spin components, and Bell inequalities other than CHSH.

## Evidence

The canonical source is `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean.json`.

Declaration statements:

- `result`: `sha256:cc5f6a00713c499dc27ac86cf567fad19c19c8377ea27eaf2773ab56e16a07c3`;
- `claim`: `sha256:897fbf8ae64b122696449eaae2726fca459f09afff34300f5e6e93f8435998cc`.

## Triage

Tier 1 open problem of a 2025 paper, preregistered in issue #24190 before any Lean. The spin-1 case is literature-attested in Cha and Lee (2026), arXiv:2603.10296v2; the general high-spin statement is the settlement.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge2$, every positive semidefinite trace-one complex matrix $\rho$ on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$, and all four real directions $a,c,b,d$ satisfying `unit`, the complex trace satisfies $|\operatorname{tr}(\rho\mathcal B)|\le n^2/2$ for the defined linear-spin CHSH operator.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Decisive mechanism.* For $n\ge2$, a positive semidefinite trace-one $\rho$ and four unit real directions, `slot_compression`, `slot_hermitian`, `slot_square` and `slots_commute` at distinct slots 0 and 1 give the construction in the Route; `lifted_square` supplies $L^2=4I$. The isometry `dilation_isometry` and density statement `dilated_density` carry the entire density matrix, so all four correlations belong to one common state. No separability hypothesis is used. The two distinct slots required by this construction are unavailable when $n=1$.
- *Sharpness over states and directions.* For any natural $n\ge2$, take the product vector $|0\rangle\otimes|0\rangle$ in the repository basis and set all four directions to $e_z$. Then $\mathcal B=2J_z\otimes J_z$, and $J_z|0\rangle=(n/2)|0\rangle$, giving expectation $n^2/2$. Thus the uniform bound cannot be reduced; this does not assert saturation for every fixed state.
- *Unequal spins.* For natural $n\ge2$ and $m\ge1$, put $s_A=n/2$ and $s_B=m/2$. For a positive semidefinite trace-one state on $\mathbb C^{n+1}\otimes\mathbb C^{m+1}$ and four unit real directions, the prose extension is the bound $nm/2=2s_As_B$. Indeed, use $D_n\otimes D_m$, slots 0 and 1 on Alice, and slot 0 for both Bob settings. `dicke_isometry` and `slot_compression` apply separately to the two factors. The unit hypotheses supply four Hermitian involutions by `slot_hermitian` and `slot_square`; Alice's pair commutes by `slots_commute` because its slots differ. `LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes` therefore gives $L^2=4I$ even when Bob's pair does not commute. The positive semidefinite trace-one dilated state and `density_involution_bound` give the bound 2 before multiplication by $(n/2)(m/2)$. This is a prose extension, not an additional compiled conclusion of `result`.
- *Effect on the source.* At $n=2$, the theorem supplies the nonviolation assertion for every two-qutrit density matrix. Consequently §5's conjecture, its all-pure-state consequence and its mixed-state consequence have the required CHSH bound. In the source's maximum-based notation, the four unit spheres form a nonempty compact parameter space and the trace modulus is continuous, so its maximum exists and is at most $2s^2$; dividing by $2s^2>0$ gives $\gamma_s\le1$. This maximum argument and the notation bridge are not formalized in the module. The source's separate question about maximizing over all traceless qudit observables, and its formulas comparing concurrence with spin-CHSH parameters, are outside this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The web searches, Semantic Scholar citation listing, 61-record arXiv search, repository search and reading of Sandhir and Ravishankar (2016), arXiv:1602.04905, are reports in #24190 rather than independently reproduced searches or readings. The directly checked literature consists of the quoted sections of Hanotel and Loubenets (2025), arXiv:2503.05172v2; the spin definitions, CHSH bound and Theorem 1 of Loubenets and Hanotel (2025), arXiv:2412.03470v2; and the theorem, proof, corollary and Discussion of Cha and Lee (2026), arXiv:2603.10296v2. The source authors' random-state experiments are not independently reproduced or used as evidence for the universal theorem.

The normalization used for the source-notation consequence is $\gamma_s=\Upsilon/(2s^2)$ from the companion paper, Corollary 1. In the spin-1 paper, the display with TeX label `1_12` identifies $\gamma_1$ with the unnormalized CHSH maximum, omitting the factor $1/2$ required by its Proposition 1 and Corollary 1; that display is not used.

The source-to-repository basis correspondence, uniform-bound sharpness, unequal-spin extension, compactness argument and source-notation consequences are prose arguments, not additional compiled assertions. No exact maximum for each fixed state, general Bell-locality statement or conclusion about nonlinear spin observables is supplied by `result`. Those questions remain outside the formal claim.
