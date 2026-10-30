---
slug: hanotel-loubenets-2025-high-spin-chsh-nonviolation
bibkey: hanotelloubenets2025chshspinone
doi: 10.1088/1402-4896/adcc66
url: https://arxiv.org/abs/2503.05172v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result
---

# Linear spin measurements do not violate CHSH for any spin at least one

## Problem

L. Hanotel and E. R. Loubenets, *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*, Phys. Scr. 100, 055115 (2025), arXiv:2503.05172v2, Introduction, `Final_Revision_Hanotel_Loubenets.tex`, line 201:

> However, up to the moment the problem whether or not the CHSH inequality is violated under Alice and Bob high spin $s\geq1$ measurements is still open -- though specifically this Bell inequality has been used for proving \cite{1, Lou.Kuz.Han:24}  nonlocality of every pure nonseparable two-qudit state.

Section 5, “Conjecture”, lines 913–914, states the spin-1 conjecture:

> Under local Alice and Bob spin-$1$ measurements in an arbitrary nonseparable pure two-qutrit state, the
> CHSH inequality is not violated.

For a physical spin $s=n/2$, with integer $n\ge2$, write $S_u=u_xS_x+u_yS_y+u_zS_z$ for a unit vector $u\in\mathbb R^3$. The operators and normalization are those of E. R. Loubenets and L. Hanotel, *High-spin measurements in an arbitrary two-qudit state*, J. Phys. A: Math. Theor. 58, 265304 (2025), arXiv:2412.03470v2, Section 2: `Revision_Loubenets_Hanotel.tex`, lines 210–250, 252–266 and 348–363. Define

$\mathcal B(a,c;b,d)=S_a\otimes S_b+S_a\otimes S_d+S_c\otimes S_b-S_c\otimes S_d$.

Issue [#24190](https://github.com/the-omega-institute/trureturing/issues/24190) fixes the reading: for every integer $n\ge2$, every positive semidefinite complex matrix $\rho$ on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$ with $\operatorname{tr}\rho=1$, and every four unit real directions $a,c,b,d$,

$\left|\operatorname{tr}(\rho\mathcal B(a,c;b,d))\right|\le n^2/2=2s^2$.

This is proved. The bound uses the spin outcomes in $[-s,s]$, without rescaling them to $[-1,1]$.

## Motivation

The question separates entanglement from CHSH violation when measurements are restricted to physical linear spin components. The source's Section 5 derives nonviolation for all mixed two-qutrit states conditionally on its pure-state conjecture. The general high-spin question asks whether increasing spin supplies a violation within this measurement family; the settlement excludes it for every allowed spin $s\ge1$ and every state.

## Gap

The bounded literature check in #24190 concerns the general high-spin assertion:

- Hanotel and Loubenets (2025, arXiv:2503.05172v2) state the high-spin question and the spin-1 conjecture at the locations quoted above.
- Loubenets and Hanotel (2025, arXiv:2412.03470v2), Theorem 1 and Corollary 1, express the fixed-state optimum through two singular values of its spin correlation matrix, with the general Tsirelson upper bound; those statements do not supply the high-spin nonviolation bound.
- H. Cha and J. Lee (2026), *CHSH inequality always holds in bipartite qutrits with spin-1 observables*, arXiv:2603.10296v2, Theorem and Corollary (`apssampv1.tex`, lines 263–269 and 547–549), establish the spin-1 case for every two-qutrit density operator and all unit directions. Their Discussion is restricted to spin 1. That case is literature-attested; the remaining general range is $n\ge3$.
- The preregistration's orchestrator reports a singlet-restricted reading of Sandhir and Ravishankar (2016, arXiv:1602.04905), web searches for high-spin CHSH nonviolation, and a repository search with no existing general settlement. The search seat reported a Semantic Scholar citation check and an arXiv search over 61 records, with no general proof found.

For the general assertion: `not-found-in-searched-scope`.

## Route

The following helper names belong to the canonical module; the helpers are private.

1. **Isometric embedding.** For every natural $n$, `dicke_isometry` proves $D_n^\dagger D_n=I$, where $D_n|k\rangle=\binom nk^{-1/2}\sum_{|x|=k}|x\rangle$, $0\le k\le n$, and $x$ ranges over subsets of the $n$ qubit slots. For every natural $n$, `dilation_isometry` proves the same identity for $V_n=D_n\otimes D_n$.
2. **Compression of a slot.** For every natural $n$, every slot $r\in\mathrm{Fin}\,n$ and every real direction $u\in\mathbb R^3$, `slot_compression` proves $D_n^\dagger P_r(u)D_n=(2/n)S_u$, where $P_r(u)$ is the Pauli component on slot $r$. No unit-direction hypothesis is needed for this identity. For the same $n,r,u$, `slot_hermitian` gives Hermiticity; `slot_square` gives $P_r(u)^2=I$ when $u$ is unit. For slots $r,t\in\mathrm{Fin}\,n$ with $r\ne t$ and any real directions $u,v$, `slots_commute` gives commutation of $P_r(u)$ and $P_t(v)$.
3. **Two distinct settings.** For $n\ge2$ and any four real directions, `chsh_dilation` proves $\mathcal B=(n/2)^2V_n^\dagger L V_n$, where $L$ is `liftedOperator` with slots 0 and 1 assigned to each party's two settings. Under the same hypotheses, `lifted_hermitian` gives Hermiticity of $L$. With all four directions additionally unit, `lifted_square` proves $L^2=4I$.
4. **Density expectation.** For every natural $n$ and every positive semidefinite $\rho$ with trace one, `dilated_density` gives positive semidefiniteness and trace one of $\tau=V_n\rho V_n^\dagger$. On any finite index type with decidable equality, `density_involution_bound` proves $|\operatorname{tr}(\tau L)|\le2$ for positive semidefinite trace-one $\tau$ and Hermitian $L$ satisfying $L^2=4I$. For $n\ge2$, positive semidefinite trace-one $\rho$, and four unit real directions, `expectation_bound` transfers this estimate through the dilation and gives $(n/2)^2\cdot2=n^2/2$. The declaration `result : claim` applies this bound.

## Falsifier

A counterexample to the registered assertion would require an integer $n\ge2$, a positive semidefinite trace-one density matrix and four unit real directions with expectation modulus greater than $n^2/2$ for exactly these linear spin matrices.

The source-to-formal correspondence is explicit. With the source's basis index $m=k+1$, its matrices have

$(S_z)_{kk}=n/2-k$, $\quad(S_x)_{k,k+1}=\sqrt{(k+1)(n-k)}/2$, $\quad(S_y)_{k,k+1}=\sqrt{(k+1)(n-k)}/(2i)$,

for $0\le k\le n$ on the diagonal and $0\le k<n$ off the diagonal, with the conjugate lower entries. These are the entries of `Jz n`, `Jx n` and `Jy n` in `PrecessionSpinOneSeparableBound`; the radicand in `Jplus` reduces to $(k+1)(n-k)$. The reused `spinComponent n u` is exactly the real linear combination of these three matrices. The definition `unit` requires the sum of the three coordinate squares to equal one, `chshOperator` has the source's four signs, and `claim` uses the complex modulus of the trace.

The assertion excludes spin $1/2$, nonlinear functions or outcome binning of spin observables, unrestricted qudit observables and Bell inequalities other than CHSH.

## Evidence

The canonical source is `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/HighSpinCHSHNonviolation.lean.json`.

Declaration statements:

- `result`: `sha256:cc5f6a00713c499dc27ac86cf567fad19c19c8377ea27eaf2773ab56e16a07c3`;
- `claim`: `sha256:897fbf8ae64b122696449eaae2726fca459f09afff34300f5e6e93f8435998cc`.

## Triage

Tier 1 open question of a 2025 paper, preregistered in issue #24190 before any Lean. Its spin-1 special case is settled by Cha and Lee (2026, arXiv:2603.10296v2); the general high-spin question is the registered target.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge2$, every positive semidefinite complex matrix $\rho$ on $\mathbb C^{n+1}\otimes\mathbb C^{n+1}$ with trace one, and every four real directions whose coordinate squares each sum to one, the complex modulus of $\operatorname{tr}(\rho\mathcal B)$ is at most $n^2/2$, with $\mathcal B$ defined by the four linear-spin tensor products above.

**Computed, not formalized**: None.

**Argued, not formalized**:

- *Decisive mechanism.* For $n\ge2$, each party's two unit directions can use distinct qubit slots. The compression identity `slot_compression` applies to every real direction and every slot; `slots_commute` applies to distinct slots. Thus both normalized spin components have commuting representatives on one common dilation, even though the spin components themselves need not commute. For four unit directions and $n\ge2$, `lifted_square` gives $L^2=4I$; `dilated_density` retains positive semidefiniteness and trace one for any such original density matrix. The bound therefore uses no separability assumption and treats pure and mixed states together. Compression is not asserted to preserve products of local spin components.
- *Sharpness of the uniform constant.* For every integer $n\ge2$, choose all four directions equal to $e_z$ and the rank-one density on the unit basis vector $|0\rangle\otimes|0\rangle$. This density is positive semidefinite and trace one. The four terms reduce to $\mathcal B=2J_z\otimes J_z$, and $J_z|0\rangle=(n/2)|0\rangle$, so its expectation is exactly $n^2/2$. Thus the uniform constant cannot be decreased. This attainment statement is not part of `result`.
- *Boundary at spin $1/2$.* At $n=1$, the definitions give $S_u=(u\cdot\sigma)/2$. Choose $a=e_z$, $c=e_x$, $b=(e_z+e_x)/\sqrt2$ and $d=(e_z-e_x)/\sqrt2$. The CHSH operator is $(\sqrt2/4)(\sigma_z\otimes\sigma_z+\sigma_x\otimes\sigma_x)$. The unit singlet vector $(|01\rangle-|10\rangle)/\sqrt2$ is an eigenvector of both tensor products with eigenvalue $-1$, giving expectation modulus $\sqrt2/2>1/2$. The restriction $n\ge2$ cannot be dropped; the two-distinct-slot construction is unavailable at $n=1$.
- *Effect on the source.* At $n=2$ the pointwise bound gives nonviolation for every two-qutrit density matrix, including the nonseparable pure states of the source's Section 5 conjecture and its mixed-state conclusion at lines 917–943. To express this in the source's parameter, the four unit-vector domains are nonempty and compact, and the absolute trace expectation is continuous, so their maximum exists and is at most 2. Dividing by the spin-1 local bound 2 gives $\gamma_1\le1$. Consequently that mixed-state conclusion requires no unproved pure-state nonviolation assumption. The same pointwise-to-maximum argument gives $\gamma_s\le1$ for every physical spin $s\ge1$; the source's separate concurrence formulas and entanglement comparisons are not certified by this settlement.
- *Neighbouring questions.* The source's fixed-state singular-value optimization formula concerns the exact optimum of an individual state, which `result` does not identify. Characterizing equality for prescribed directions, and deciding what nonlinear spin measurements or other Bell inequalities can detect, require additional statements beyond this CHSH bound.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The quoted Hanotel–Loubenets source, the companion's spin definitions and optimization statements, and the stated scope of Cha–Lee's theorem were checked in their versioned TeX sources. The preregistration's orchestrator reading of Sandhir–Ravishankar, its web and repository searches, and the search seat's Semantic Scholar listing and 61-record arXiv search were not independently reproduced; their reported absence of a general settlement is `ASSUMED-UNVERIFIED` outside the source readings specified here.

All claims in “Argued, not formalized”, including attainment, the spin-$1/2$ example, existence and bounds of the source's maxima, and consequences for its CHSH parameter, are mathematical arguments outside the compiled type of `result`. The source's numerical study was not reproduced and is not used as evidence for the universal bound. No independent verification of its state-specific concurrence or CHSH-parameter calculations is claimed. Equality classifications for prescribed directions and conclusions about nonlinear measurements or other Bell inequalities remain open in this dossier.
