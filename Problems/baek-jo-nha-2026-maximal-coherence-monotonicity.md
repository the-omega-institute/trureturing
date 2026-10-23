---
slug: baek-jo-nha-2026-maximal-coherence-monotonicity
bibkey: baekjonha2026maximalcoherence
doi: null
url: https://arxiv.org/abs/2607.05847v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result
---

## Problem

Baek, Jo and Nha, *Maximal coherence of quantum measurement and the resource theory of sharpness*, arXiv:2607.05847v1, asks whether $C_D^{\max}$ remains monotone under general CP unital maps for non-dichotomic POVMs. Table I marks the corresponding entry under any fuzzifying operations as open.

## Motivation

The question concerns the spectral distance $D_\infty$ and the tetrahedral SIC qubit POVM. The settling declaration is `D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone.result`.

## Gap

The source leaves the general CP-unital, dimension-changing case unresolved. The settlement supplies a four-outcome counterexample using the discarding dual $J(X)=X\otimes I_2$.

## Route

The module defines POVMs, incoherent POVMs, $D_\infty$, fixed-basis coherence, maximal coherence, CP-unital duals and the source claim. It constructs the tetrahedral SIC effects, proves the simultaneous-basis upper bound $C_{D_\infty}^{\max}(\mathsf M_{\rm SIC})\le\frac12\sqrt{2/3}$, proves the Bell-basis lower bound $C_{D_\infty}^{\max}(J(\mathsf M_{\rm SIC}))\ge\frac12$, and derives `result : ¬ claim`.

The coordinates choose $\mathbb C^2\otimes\mathbb C^2\cong$ `Fin 4` through `finProdFinEquiv`, $(i,j)\mapsto2i+j$, in the order $|00\rangle,|01\rangle,|10\rangle,|11\rangle$. The module uses `open scoped ComplexOrder` for the complex positive-semidefinite calculations; these are Lean elaboration choices preserving the source meaning.

## Falsifier

The claim is falsified by the instance $d=2$, $e=4$, $n=4$, $\alpha=1$, $q_x=1/4$, the tetrahedral SIC POVM and $J$. The strict inequality $\frac12>\frac12\sqrt{2/3}$ is the final contradiction.

## Evidence

The SIC upper bound `sic_cmax_upper`, SIC ancilla lower bound `sic_ancilla_cmax_lower`, and refutation `result` are kernel-checked in Lean; the axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The general ancilla mechanism is proved in prose below. The stabilization statement $C_D^{\max}(\mathsf P\otimes I_d)=S_D(\mathsf P)$ and the characterization for jointly convex distances are paper arguments from the preregistration's Consequences. The uniform $A_i(t)$ bounds and full-rank statement have the prose proof below; they are not Lean declarations in this module.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Computed evidence: [`check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/e79e3f95fef7b48c4474dbaf42991a0601a8dd05/docs/reports/baek-jo-nha-2026-maximal-coherence-ancilla-nonmonotone), run as `python3 check.py`, exit 0, SHA-256 `b0d07f99a84ffde3e5a0285f79184a2e0dfe8cf0dcf4ad2c8c151bc7d971d96c`, reports `bad= 0`. Its family calculations evaluate only $t=1$: POVM and Kraus checks, the sharpness value $1/2$, 20,000 random qubit unitaries (sampled maximum dephasing distance $0.408247$, bound $0.408248$), and 20,000 random Bell-diagonal POVMs (sampled minimum distance $0.610942$, with the trivial POVM attaining $1/2$). Separately, it samples stabilization on 200 random qubit POVMs, using 3,000 trivial competitors and 300 Bell-diagonal competitors per POVM, with tolerance $10^{-3}$. These finite samples do not compute the uniform $0<t\le1$ family.

## Triage

| item | status | evidence |
|---|---|---|
| For a POVM on $\mathbb C^d$, tensoring $I_d$ and choosing a maximally entangled Bell basis forces every incoherent competitor to a trivial POVM under normalized partial trace; the coherence in that basis is at least sharpness. | proved | Proved in prose: the general ancilla derivation below, assuming unitary invariance and CP-unital contractivity of $D$. |
| For every unitarily invariant, CP-unital-contractive distance, $C_D^{\max}(\mathsf P\otimes I_d)=S_D(\mathsf P)$. | proved | Proved in prose: stabilization derivation below, with unitary invariance and CP-unital contractivity. |
| For jointly convex such $D$, monotonicity under all fuzzifying operations iff $C_D^{\max}=S_D$ on every POVM. | proved | Proved in prose: characterization derivation below; sharpness monotonicity gives sufficiency, and stabilization gives necessity. |
| For $A_i(t)=(I+t\,\vec n_i\cdot\vec\sigma)/4$, $0<t\le1$, $C_{D_\infty}^{\max}(A(t))\le\frac t2\sqrt{2/3}$. | proved | Proved in prose: the family upper-bound and attainment derivation below. |
| For $0<t\le1$, $C_{D_\infty}^{\max}(J(A(t)))\ge\frac t2$. | proved | Proved in prose: the family lower-bound derivation below, using both Rayleigh signs and eigenvalues $(1\pm t)/4$. |
| For $0<t\le1$, the increase equals $\frac t2(1-\sqrt{2/3})>0$; every effect is full rank for $0<t<1$. | proved | Proved in prose: attainment of both bounds and positive eigenvalues, as derived below. |
| The family instance $t=1$ refutes general CP-unital monotonicity. | proved | Kernel-checked `result : ¬ claim`, with `sic_cmax_upper` and `sic_ancilla_cmax_lower` on its proof path. |
| Numerical checks of the family instance $t=1$. | computed | The pinned experiment entry above: `python3 check.py`, exit 0, SHA-256 `b0d07f99a84ffde3e5a0285f79184a2e0dfe8cf0dcf4ad2c8c151bc7d971d96c`, `bad= 0`, over exactly the stated finite samples. |
| Whether $C_\diamond^{\max}(\mathsf M_{\rm SIC})<S_\diamond(\mathsf M_{\rm SIC})$. | open | No Lean declaration or computation in this delivery addresses the diamond distance. |
| Whether monotonicity also fails for dimension-preserving fuzzifying operations. | open | Unresolved: the counterexample changes dimension from $2$ to $4$; no dimension-preserving counterexample is established here. |

### General ancilla mechanism, stabilization and characterization: prose proof

Let $\mathsf P=\{P_x\}$ be a POVM on $\mathbb C^d$, $d\ge1$, and let $D$ be unitarily invariant and contractive under CP-unital maps. Set $J_d(X)=X\otimes I_d$ and $R_d(Y)=\operatorname{Tr}_2(Y)/d$. For the embeddings $V_j\psi=\psi\otimes|j\rangle$, $J_d(X)=\sum_jV_jXV_j^\dagger$ with $\sum_jV_jV_j^\dagger=I_{d^2}$, and $R_d(Y)=d^{-1}\sum_jV_j^\dagger YV_j$ with $d^{-1}\sum_jV_j^\dagger V_j=I_d$. These Kraus forms make both maps CP unital, and $R_dJ_d=\mathrm{id}$. For $a,b\in\{0,\ldots,d-1\}$, choose the Bell vectors

$$|\Phi_{ab}\rangle=\frac1{\sqrt d}\sum_{k=0}^{d-1}e^{2\pi iak/d}|k\rangle\otimes|k+b\pmod d\rangle.$$

Their inner products are $\delta_{b,b'}d^{-1}\sum_k e^{2\pi i(a'-a)k/d}=\delta_{b,b'}\delta_{a,a'}$, where primes distinguish the second vector, so the $d^2$ vectors form an orthonormal basis. Taking the partial trace kills the terms with different second coordinates, giving $\operatorname{Tr}_2(|\Phi_{ab}\rangle\langle\Phi_{ab}|)=d^{-1}\sum_k|k\rangle\langle k|=I_d/d$. If $U_B$ has these columns and $\mathsf B$ is any incoherent POVM on $\mathbb C^{d^2}$, write $Y_x=U_BB_xU_B^\dagger$. Each $Y_x$ is a nonnegative combination of Bell projectors, so

$$R_d(Y_x)=q_xI_d,\qquad q_x=\frac{\operatorname{Tr}(B_x)}{d^2}\ge0,\qquad \sum_xq_x=1.$$

Unitary invariance and contractivity therefore give, for every such competitor,

$$D(U_B^\dagger J_d(\mathsf P)U_B,\mathsf B)
=D(J_d(\mathsf P),\mathsf Y)
\ge D(\mathsf P,\{q_xI_d\})\ge S_D(\mathsf P).$$

Taking the incoherent infimum proves the general mechanism: Bell-basis coherence is at least sharpness. This is a prose proof for general $d$, $\mathsf P$ and $D$. Lean's `R_bell_diag` checks the scalar partial-trace identity only on $\mathbb C^4$; `sic_bell_distance_lower` and `sic_ancilla_cmax_lower` check the spectral-distance lower bound only for the SIC instance.

For stabilization, trivial POVMs are incoherent in every basis, so unitary invariance gives $C_D^{\max}(\mathsf Q)\le S_D(\mathsf Q)$. For each probability vector $q$, contractivity of $J_d$ and $R_d$ in opposite directions gives

$$D(J_d(\mathsf P),\{q_xI_{d^2}\})=D(\mathsf P,\{q_xI_d\}).$$

Taking infima gives $S_D(J_d(\mathsf P))=S_D(\mathsf P)$. Combined with the Bell lower bound, this proves in prose

$$C_D^{\max}(\mathsf P\otimes I_d)=S_D(\mathsf P).$$

For characterization, assume additionally that $D$ is jointly convex. A fuzzifying operation $F(\mathsf P)_x=\alpha\Phi(P_x)+(1-\alpha)q_xI$ takes a trivial competitor $T_x=p_xI$ to the trivial POVM $F(\mathsf T)_x=(\alpha p_x+(1-\alpha)q_x)I$. Joint convexity, contractivity and $D(\{q_xI\},\{q_xI\})=0$ imply

$$D(F(\mathsf P),F(\mathsf T))\le\alpha D(\Phi(\mathsf P),\Phi(\mathsf T))\le D(\mathsf P,\mathsf T).$$

Taking infima proves sharpness monotonicity. Hence $C_D^{\max}=S_D$ on every POVM is sufficient for monotonicity under all fuzzifying operations. Conversely, monotonicity applied to $J_d$ and stabilization gives

$$S_D(\mathsf P)=C_D^{\max}(J_d(\mathsf P))\le C_D^{\max}(\mathsf P)\le S_D(\mathsf P),$$

which proves necessity. This equivalence is proved in prose with the stated distance hypotheses.

### The $t$-family: prose proof

Use the tetrahedral vectors of #15378 and put $A(t)=\{A_i(t)\}_{i=1}^4$, where

$$A_i(t)=\frac{I+t\,\vec n_i\cdot\vec\sigma}{4}
=tA_i(1)+(1-t)\frac I4,\qquad 0<t\le1.$$

Since $\|\vec n_i\|=1$, the Hermitian matrix $\vec n_i\cdot\vec\sigma$ has eigenvalues $\pm1$. Thus $A_i(t)$ has eigenvalues $(1\pm t)/4$, is positive semidefinite, and is positive definite for $0<t<1$. Also $\sum_i\vec n_i=0$, so $\sum_i A_i(t)=I$. This is a four-outcome POVM throughout the stated interval, with full-rank effects for $t<1$.

**Upper bound.** Fix one unitary $U$ common to all four effects and let $B_i(t)$ be the diagonal part of $U^\dagger A_i(t)U$. Positivity and completeness make $B(t)$ an incoherent POVM. The identity term has zero off-diagonal entries, so

$$(U^\dagger A_i(t)U)_{01}=t(U^\dagger A_i(1)U)_{01}.$$

A Hermitian $2\times2$ matrix with zero diagonal has spectral norm equal to the modulus of its off-diagonal entry. Route step 1 of #15378 gives $\sum_i|(U^\dagger A_i(1)U)_{01}|^2=1/6$. Cauchy–Schwarz therefore gives

$$C_{D_\infty}(U^\dagger A(t)U)
\le D_\infty(U^\dagger A(t)U,B(t))
=\frac t2\sum_i|(U^\dagger A_i(1)U)_{01}|
\le\frac t2\sqrt{\frac23}.$$

The bound holds for every common $U$, hence $C_{D_\infty}^{\max}(A(t))\le\frac t2\sqrt{2/3}$.

**Lower bound.** Let $U_B$ be the Bell-basis unitary and let $B$ be any incoherent four-outcome POVM on $\mathbb C^4$. Write $Y_i=U_B B_i U_B^\dagger$, $R=\operatorname{Tr}_2/2$ and $q_i=\operatorname{Tr}(B_i)/4$. Bell projectors have normalized partial trace $I_2/4$, so $R(Y_i)=q_i I_2$; positivity and completeness give $q_i\ge0$ and $\sum_i q_i=1$. Since $R(J(A_i(t)))=A_i(t)$, for $Z_i=J(A_i(t))-Y_i$ and every unit vector $\psi$,

$$\left|\langle\psi|R(Z_i)|\psi\rangle\right|
=\left|\frac12\sum_{j=0}^1\langle\psi\otimes j|Z_i|\psi\otimes j\rangle\right|
\le\|Z_i\|_\infty.$$

This is the two-sided Rayleigh bound, obtained by applying the bound to both $Z_i$ and $-Z_i$, as in route step 2. Taking eigenvectors of $A_i(t)$ and using unitary invariance of the norm yields

$$\|U_B^\dagger J(A_i(t))U_B-B_i\|_\infty
\ge\max\left\{\left|\frac{1+t}{4}-q_i\right|,\left|\frac{1-t}{4}-q_i\right|\right\}
\ge\frac t4.$$

The last inequality follows because the two eigenvalues differ by $t/2$, and their distances to any real $q_i$ sum to at least $t/2$. Summing over all four effects with the factor $1/2$ in $D_\infty$ gives $D_\infty(U_B^\dagger J(A(t))U_B,B)\ge\frac12\cdot4\cdot\frac t4=\frac t2$. Taking the infimum over $B$ and then including $U_B$ in the unitary supremum gives $C_{D_\infty}^{\max}(J(A(t)))\ge\frac t2$.

**Attainment and increase.** For a qubit basis with reference axis $x$, all four tetrahedral effects have off-diagonal modulus $t\sqrt{2/3}/4$. Every diagonal competitor leaves this entry unchanged, and the spectral norm of its difference from the effect is at least that modulus. The dephased competitor attains it for every effect, so the coherence in this basis is $t\sqrt{2/3}/2$. This attains the uniform upper bound. For $J(A(t))$, the trivial competitor $I_4/4$ has effectwise distance $\|J(A_i(t))-I_4/4\|_\infty=t/4$, giving $C_{D_\infty}^{\max}(J(A(t)))\le t/2$ in every basis. This attains the Bell lower bound. Thus

$$C_{D_\infty}^{\max}(A(t))=\frac t2\sqrt{\frac23},\qquad
C_{D_\infty}^{\max}(J(A(t)))=\frac t2.$$

Subtracting gives

$$C_{D_\infty}^{\max}(J(A(t)))-C_{D_\infty}^{\max}(A(t))
=\frac t2\left(1-\sqrt{\frac23}\right)>0,$$

because $t>0$ and $\sqrt{2/3}<1$. The operation $J(X)=X\otimes I_2$ is the same CP-unital dual as at $t=1$, so every member of the family violates monotonicity, including the full-rank members with $t<1$.

The conventions are the source's Section II.A coherence, Section III.A common-unitary maximal coherence, Eq. (32) spectral distance and Eq. (12) fuzzifying operations, with the SIC of Section IV.A. They agree with Lean's `IsPOVM`, `IsIncoherent`, `dInf`, `coh`, `cmax` and `IsCPUnitalDual`: the proof uses an incoherent POVM for the upper infimum, all incoherent competitors for the lower infimum, one common unitary for each basis choice, and the distance factor $1/2$. The uniform argument is a prose proof; `result` and its live SIC/Bell bounds check only $t=1$ in Lean.

### What the settlement shows

The general CP-unital monotonicity question is refuted for non-dichotomic POVMs when the fuzzifying map may change dimension. The stabilization and characterization statements remain prose derivations with the hypotheses stated above. The diamond-distance and dimension-preserving questions remain open.

## ASSUMED-UNVERIFIED

The literature screen establishes the cited source and its open wording in the searched scope. Exhaustive worldwide novelty beyond the cited source and the recorded literature search is not claimed.
