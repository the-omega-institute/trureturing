---
slug: hanotel-loubenets-2025-high-spin-chsh-nonviolation
bibkey: hanotelloubenets2025chshspinone
doi: 10.1088/1402-4896/adcc66
url: https://arxiv.org/abs/2503.05172v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result
---

# Linear spin measurements never violate CHSH for spin at least one

## Problem

L. Hanotel and E. R. Loubenets, *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*, Phys. Scr. 100 (2025) 055115, arXiv:2503.05172v2, state in the Introduction (`Final_Revision_Hanotel_Loubenets.tex`, line 201):

> However, up to the moment the problem whether or not the CHSH inequality is violated under Alice and Bob high spin $s\geq1$ measurements is still open -- though specifically this Bell inequality has been used for proving \cite{1, Lou.Kuz.Han:24}  nonlocality of every pure nonseparable two-qudit state.

Section 5, “Conjecture” (TeX lines 913–914), states:

> Under local Alice and Bob spin-$1$ measurements in an arbitrary nonseparable pure two-qutrit state, the
> CHSH inequality is not violated.

The spin observables are specified in E. R. Loubenets and L. Hanotel, *High-spin measurements in an arbitrary two-qudit state*, J. Phys. A: Math. Theor. 58 (2025) 265304, arXiv:2412.03470v2, `Revision_Loubenets_Hanotel.tex`, lines 210–237. For $n=2s$, the single-particle space is $\mathbb C^{n+1}$ and $S_u=u_xJ_x+u_yJ_y+u_zJ_z$ for a real unit vector $u$. In the basis indexed by $k=0,\ldots,n$, $(J_z)_{kk}=n/2-k$, $(J_x)_{k,k+1}=\sqrt{(k+1)(n-k)}/2$, and $(J_y)_{k,k+1}=\sqrt{(k+1)(n-k)}/(2i)$, with $J_z$ diagonal, $J_x$ and $J_y$ zero on the diagonal and at nonadjacent indices, and their lower adjacent entries the conjugates of the displayed upper entries. These are the repository's `Jx n`, `Jy n`, `Jz n` and `spinComponent n u`.

Issue [#24190](https://github.com/the-omega-institute/trureturing/issues/24190) fixes the general-spin reading: for every natural $n\ge2$, every positive semidefinite complex matrix $\rho$ of trace one on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$, and all four real unit directions $a,c,b,d$,
$\|\operatorname{tr}(\rho\mathcal B_n)\|\le n^2/2$, where
$\mathcal B_n=S_a\otimes S_b+S_a\otimes S_d+S_c\otimes S_b-S_c\otimes S_d$.
This is proved. It answers the high-spin question for every integer or half-integer spin $s\ge1$, including the spin-1 conjecture and mixed states. The comparison is with the source's local bound $2s^2=n^2/2$ (companion TeX lines 348–356).

The sources and conventions are recorded in [the literature note](../Library/Observer/hanotelloubenets2025chshspinone.md).

## Motivation

The question distinguishes entanglement from CHSH violation when measurements are restricted to physical spin components. The allowed operators are linear combinations of three spin matrices, rather than arbitrary bounded qudit observables. A uniform answer determines whether changing the state or increasing the spin can reveal CHSH nonlocality within this measurement family.

## Gap

The bounded literature check in #24190 records no general-spin settlement in the searched scope:

- Hanotel and Loubenets (2025), arXiv:2503.05172v2, retain the high-spin question and the spin-1 conjecture; the source passages are quoted above.
- H. Cha and J. Lee (2026), *CHSH inequality always holds in bipartite qutrits with spin-1 observables*, arXiv:2603.10296v2, state the density-operator bound for $\mathbb C^3\otimes\mathbb C^3$ (Theorem, `apssampv1.tex`, lines 263–269), with their Corollary and Discussion restricted to spin 1 (lines 547–566). This settles $n=2$, rather than the full range $n\ge2$.
- The preregistration records broader web, arXiv, citation-index and repository searches without a general-spin proof; their coverage is bounded as specified below.

`not-found-in-searched-scope`.

## Route

All lemma names below belong to `HighSpinCHSHNonviolation` unless qualified otherwise. Write $D_n$ for `dicke n`, $P_r(u)$ for `slotPauli n r u`, and $V_n=D_n\otimes D_n$ for `dilation n`. The subset basis encodes $n$ qubits, and $D_n|k\rangle=\binom nk^{-1/2}\sum_{|x|=k}|x\rangle$ for $k=0,\ldots,n$.

1. **Isometry and compression.** For every natural $n$, `dicke_isometry` proves $D_n^\dagger D_n=I$ by counting subsets of each cardinality. For every natural $n$, every slot $r\in\mathrm{Fin}\,n$ (so $n>0$), and every real direction $u$, `slot_compression` proves $D_n^\dagger P_r(u)D_n=(2/n)S_u$, without requiring $u$ to be unit. The raising and diagonal counts are `raising_compression` and `z_compression`, each with precisely the hypotheses $n\in\mathbb N$ and $r\in\mathrm{Fin}\,n$. For every natural $n$, `dilation_isometry` gives $V_n^\dagger V_n=I$.
2. **Two distinct slots.** For every natural $n$, slot $r\in\mathrm{Fin}\,n$ and real direction $u$, `slot_hermitian` makes $P_r(u)$ Hermitian; with the additional hypothesis `unit u`, `slot_square` gives $P_r(u)^2=I$. For $r,t\in\mathrm{Fin}\,n$ with $r\ne t$ and arbitrary real directions $u,v$, `slots_commute` proves that $P_r(u)$ and $P_t(v)$ commute. For $n\ge2$ and arbitrary real $a,c,b,d$, `chsh_dilation` uses slots 0 and 1 to prove $\mathcal B_n=(n/2)^2V_n^\dagger L V_n$, where $L$ is `liftedOperator n 0 1 a c b d` with these valid finite indices.
3. **Lifted square.** For $n\ge2$ and arbitrary real $a,c,b,d$, `lifted_hermitian` proves $L$ Hermitian. For $n\ge2$ and all four directions unit, `lifted_square` proves $L^2=4I$. It applies `LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes`: on finite index types with decidable equality, all four local matrices must be Hermitian involutions, and at least one local pair must commute. Here the unit-direction hypotheses provide the involutions and the distinct slots provide commutation.
4. **Density and expectation.** For every natural $n$ and every positive semidefinite $\rho$ with $\operatorname{tr}\rho=1$, `dilated_density` proves that $\tau=V_n\rho V_n^\dagger$ is positive semidefinite and has trace one. On any finite index type with decidable equality, `density_involution_bound` assumes $\tau\ge0$, $\operatorname{tr}\tau=1$, $L=L^\dagger$ and $L^2=4I$; matrix Cauchy–Schwarz gives $\|\operatorname{tr}(\tau L)\|\le2$.
5. **Original bound.** For $n\ge2$, positive semidefinite trace-one $\rho$, and four unit real directions, `expectation_bound` combines the preceding identities with cyclicity of trace to obtain $\|\operatorname{tr}(\rho\mathcal B_n)\|\le(n/2)^2\cdot2=n^2/2$. `result : claim` universally quantifies exactly these hypotheses.

## Falsifier

A violation would require some natural $n\ge2$, a positive semidefinite trace-one $\rho$, and four unit real directions with $\|\operatorname{tr}(\rho\mathcal B_n)\|>n^2/2$. The proof would not answer the source question if the spin matrices, directions, normalization or measurement family differed. The module uses:

- `unit u`, defined by $u_x^2+u_y^2+u_z^2=1$;
- the frozen linear `spinComponent`, with the matrix entries and basis correspondence specified above;
- the four tensor products with signs $+,+,+,-$, exactly as in the source's CHSH operator;
- positive semidefiniteness and complex trace one, without a purity or separability assumption;
- the complex norm of the trace expectation, equal to its absolute value, and the bound $n^2/2=2s^2$.

The theorem excludes $n=1$, and it does not substitute nonlinear functions, outcome binning or arbitrary dichotomic observables for spin components. No supremum or infimum is used in `claim`; the bound is pointwise for every allowed choice of directions.

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

**Proved by `result`:** for every natural $n\ge2$, every positive semidefinite complex matrix $\rho$ of trace one on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$, and every four real directions $a,c,b,d$ each satisfying $u_x^2+u_y^2+u_z^2=1$, the complex norm $\|\operatorname{tr}(\rho\mathcal B_n)\|$ is at most $n^2/2$, for $\mathcal B_n$ defined above.

**Computed, not formalized**. None.

**Argued, not formalized.**

- *Decisive mechanism.* For $n\ge2$, the compression in `slot_compression` represents each spin component in a real direction, divided by $s=n/2$, on either of two distinct qubit slots. For unit directions, `slot_square` makes the slot operators involutions; for distinct slots, `slots_commute` makes each local pair commute. Thus the hypotheses of `lifted_square` are available even when the compressed spin components themselves do not commute. The obstruction belongs to the permitted measurement family and applies to every density matrix.
- *Sharpness.* For every natural $n\ge2$, take all four directions along $z$ and $\rho=|0,0\rangle\langle0,0|$ in the basis above. This is a positive semidefinite trace-one matrix. The definition of `chshOperator` gives $\mathcal B_n=2J_z\otimes J_z$, and $J_z|0\rangle=(n/2)|0\rangle$, giving expectation $2(n/2)^2=n^2/2$. Thus a smaller uniform constant cannot replace the bound when repeated settings and product states are allowed. This attainment is not a conclusion of `result`.
- *Boundary at spin one half.* At $n=1$, let $|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$ and choose $a=z$, $c=x$, $b=(z+x)/\sqrt2$, $d=(z-x)/\sqrt2$. All four directions are unit. Since $J_x=\sigma_x/2$ and $J_z=\sigma_z/2$, the two singlet correlations $\langle J_x\otimes J_x\rangle$ and $\langle J_z\otimes J_z\rangle$ equal $-1/4$. The CHSH expectation is $-\sqrt2/2$, whose absolute value exceeds $n^2/2=1/2$. There is only one qubit slot, so the distinct-slot construction cannot apply.
- *Effect on the source.* Setting $n=2$ covers both the pure-state conjecture and the mixed-state conclusion in Hanotel and Loubenets (2025), arXiv:2503.05172v2, Section 5, TeX lines 913–943. With the source's definition of $\gamma_s$ as the maximum absolute CHSH expectation divided by $2s^2$, the pointwise bound implies $\gamma_s\le1$ for every integer or half-integer $s\ge1$: every value being maximized is bounded. The source's pure-state inequality and its convex-mixture extension therefore have the asserted nonviolation bound. Neither $\gamma_s$ nor its optimizing directions are defined or computed by this Lean module.
- *Neighbouring questions.* The theorem's equal-spin setting leaves unequal local spins outside its formal statement. An extension using separate Dicke maps for $n_A,n_B\ge2$ and the scale $(n_A/2)(n_B/2)$ is `open` here: its two-parameter compression and expectation statement have not been compiled. State-dependent exact maxima, Bell inequalities other than CHSH, and measurements given by nonlinear functions of spin remain outside this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The source passages and spin conventions in arXiv:2503.05172v2 and arXiv:2412.03470v2, and the stated spin-1 scope of Cha and Lee (2026), arXiv:2603.10296v2, were checked in their TeX sources. Cha and Lee's full proof was not independently verified. The broader web searches, the Semantic Scholar citation count, the 61-record arXiv search and the reading of Sandhir and Ravishankar (2016), arXiv:1602.04905, are reported in #24190 and were not independently reproduced. The source's million-state numerical study was not reproduced.

The identification of the paper's notation with the Lean definitions is a mathematical reading of the two sources, not a formal encoding of their text. All statements under “Argued, not formalized”, including general sharpness, the spin-one-half counterexample, the interpretation via $\gamma_s$ and the proposed unequal-spin extension, are not additional Lean conclusions. The unequal-spin extension and the neighbouring questions have no settlement in this dossier. No experimental realization or unrestricted Bell-locality conclusion is asserted.
