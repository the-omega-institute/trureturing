---
slug: lonigro-chruscinski-2022-dephasing-two-classicality-refutation
bibkey: lonigrochruscinski2022dephasing
doi: 10.3389/frqst.2022.1090022
url: https://arxiv.org/abs/2211.02014v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.result
---

# A block measurement refutes mutual-unbiasedness necessity for two-classical dephasing

## Problem

D. Lonigro and D. Chruściński, *On the classicality of quantum dephasing processes*, arXiv:2211.02014v2; Frontiers in Quantum Science and Technology 1, 1090022 (2022), Section 3.2, immediately following Proposition `prop:2classicality_mubs`. The v2 TeX source (`dephasing-v2.tex`, md5 `e2904085775dc9d0af3b2dba4d50c065`), line 347, states:

> It may be conjectured that this is the only measurement choice yielding a genuinely time-dependent $2$-classical process---excepting the particular case in which $\rho_{t_0}$ is maximally mixed, cf.~the discussion in the next subsection.

The antecedent is the phase-modified Fourier measurement basis of Eq. `eq:mubs`, whose squared overlaps with every dephasing basis vector are $1/d$ (TeX lines 284–289). Proposition `prop:2classicality_mubs` assumes an initial state diagonal in the dephasing basis and gives two-classicality for that measurement family, for arbitrary bath Hamiltonians and bath state (lines 326–347). The definitions and source locators are also in [the literature note](../Library/QuantumContext/lonigrochruscinski2022dephasing.md).

Issue [#21441](https://github.com/the-omega-institute/trureturing/issues/21441) fixes the following necessity statement, encoded by `claim`. For every $d,m\in\mathbb N$, every family of Hermitian bath matrices $H_j$ on $\mathbb C^m$, positive semidefinite unit-trace matrices $\sigma$ and $\rho$ on the bath and system respectively, unitary measurement matrix $V$, and initial time $t_0\in\mathbb R$, assume:

- $\rho$ is diagonal in the dephasing basis and $\rho\ne I_d/d$;
- some rank-one measurement projector $P_x=|m_x\rangle\langle m_x|$, with $m_x$ the $x$th column of $V$, does not commute with some dephasing projector $E_j=|e_j\rangle\langle e_j|$;
- for every $t_0\le t_1\le t_2$, the one-time law is normalized and both marginals of the two-time law equal the corresponding one-time law;
- for some fixed outcomes $x,y$, two ordered time pairs at or after $t_0$ give different two-time values.

The conclusion is $|V_{jx}|^2=1/d$ for every $j,x$. The laws here are the literal joint-system trace formula of the paper's Eq. (2), with Hamiltonian $\mathbf H=\sum_jE_j\otimes H_j$, propagator $e^{-i(t-s)\mathbf H}$, initial product $\rho\otimes\sigma$, and system Lüders operations $X\mapsto(P_x\otimes I_m)X(P_x\otimes I_m)$. There is no bath reset. The definitions `prob1` and `prob2` take values in $\mathbb C$; `twoClassical` imposes the stated normalization and marginal equalities. No positive lower bound on $d$ or $m$ is added to `claim`.

This is a consequence of the conjectured necessity: it restricts to finite baths and time-independent Hamiltonians, asks only for unbiasedness rather than membership in the named Fourier family, and additionally requires actual nonconstancy of the two-time law. It is refuted.

## Motivation

Two-classicality means that at most two sharp measurements do not reveal a violation of Kolmogorov consistency. The source asks whether time dependence without such a violation requires measurements unbiased across the whole dephasing basis. An answer distinguishes a global measurement requirement from consistency that can arise separately within invariant subspaces; it also separates two-time tests from full classicality of the multitime statistics.

## Gap

The bounded literature check recorded in #21441 reports:

- the v2 source retains the quoted conjecture;
- the orchestrator's OpenAlex record W4311873358 lists seven citing works;
- the search agent's Semantic Scholar screen of eight citing records found neither a proof of the necessity nor this refutation; two published APS versions were inaccessible with HTTP 401.

The citation sets are reported searches, not an exhaustive census. The search outcome is `not-found-in-searched-scope`.

## Route

Every lemma named below belongs to the designated module; the helper declarations are private. Fix throughout this route $d=3$, $m=2$, $t_0=0$, and

$$
Z=\operatorname{diag}(1,-1),\qquad
(H_0,H_1,H_2)=(0,Z,2Z),\qquad
\sigma=I_2/2,\qquad
\rho=\operatorname{diag}(1/2,1/3,1/6),
$$

with measurement columns $m_0=(e_0+e_1)/\sqrt2$, $m_1=(e_0-e_1)/\sqrt2$, $m_2=e_2$.

1. **Admissible data.** `measurement_unitary` proves that this specific measurement matrix is unitary. `states_valid` certifies positive semidefiniteness and unit trace of these two states, diagonality of this $\rho$, and $\rho\ne I_3/3$. `blocks_hermitian` proves Hermiticity of each of these three bath blocks.
2. **Actual joint dynamics.** `hamiltonian_diagonal` identifies the Hamiltonian of these blocks with the diagonal energies $E_{(j,b)}=j$ for $b=0$ and $-j$ for $b=1$. For every real $t$, `propagator_diagonal` identifies its matrix exponential with diagonal entries $e^{-itE_k}$. For every real $t$, every complex matrix $X$ on $\mathbb C^3\otimes\mathbb C^2$, and every joint pair of indices $k,l$, `evolution_entries` gives $(UXU^\dagger)_{kl}=e^{-it(E_k-E_l)}X_{kl}$ for this propagator. `initial_stationary` states that this evolution fixes the particular product $\rho\otimes\sigma$ for every real $t$.
3. **Literal trace evaluation.** For every $x\in\{0,1,2\}$, `post_measurement` gives the unnormalized joint state $p_xP_x\otimes\sigma$, where $p=(5/12,5/12,1/6)$. For every real $t$ and outcome $y$, `one_time` gives $\mathbb P_1(y,t)=p_y$. For all real $t_1,t_2$ and outcomes $x,y\in\{0,1,2\}$, `two_time` identifies $\mathbb P_2(y,t_2;x,t_1)$ with the $(y,x)$ entry of

   $$
   J(u)=\begin{pmatrix}a(u)&b(u)&0\\b(u)&a(u)&0\\0&0&1/6\end{pmatrix},\qquad u=t_2-t_1,
   $$

   $$
   a(u)=\frac{5(2+e^{iu}+e^{-iu})}{48},\qquad
   b(u)=\frac{5(2-e^{iu}-e^{-iu})}{48}.
   $$

4. **Consistency and nonconstancy.** `consistency` proves `twoClassical` for precisely these data: normalization and both marginal identities for every $0\le t_1\le t_2$. `dependence` proves `timeDependent` for these data using $x=y=0$ and the ordered time pairs $(0,0)$ and $(0,\pi)$, whose two-time values are $5/12$ and $0$.
5. **Contradiction.** `incompatible` proves noncommutation for this measurement, using $P_0$ and $E_0$. `biased` proves $|V_{20}|^2\ne1/3$: that entry is zero. Applying the universal `claim` to these fixed data would give $|V_{20}|^2=1/3$. The theorem `result : ¬ claim` derives the contradiction.

## Falsifier

The refutation would miss the source if it substituted a reduced-channel regression formula for the intervened joint dynamics, allowed an invalid measurement or state, omitted an ordered-time consistency requirement, or used only a constant process. The module uses the full matrix exponential and joint Lüders traces, certifies the unitary measurement and density conditions, proves normalization and both marginals for all ordered times, and exhibits different two-time values. The nonzero commutator and zero overlap separately exclude full compatibility and mutual unbiasedness. The conclusion does not assert consistency at three or more measurements.

## Evidence

The canonical source is `D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.lean` (336 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.lean.json`, statement `sha256:6239f247d02d5871a9753ccb7eb36b9df0bdee916554f56c239a39bc5e5cdafe`.

Declaration statements:

- `result`: `sha256:b8743a1b52e9c16bcca9ad96ed93b200be2f4998f4d3cbf18cce8145e932cec7`;
- `claim`: `sha256:773533162c0bafbbcbbe2ac1860f8a61d5c83df808b2ea2d016d15319319c7eb`.

## Triage

Tier 1 conjecture of a 2022 journal paper, preregistered in issue #21441 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal implication `claim` is false. Across finite system and bath dimensions, Hermitian bath blocks, positive semidefinite unit-trace bath and system states with the system state diagonal and not maximally mixed, a noncommuting rank-one measurement, consistency through two measurements for all ordered times, and a nonconstant two-time law do not together force every squared measurement overlap to equal $1/d$.

**Computed, not formalized** (exact symbolic evaluation of the joint trace formula by the dossier seat; the orchestrator reproduced every item below with an independent script):

- For the displayed witness, the six Hamiltonian energies are $(0,0,1,-1,2,-2)$. Symbolic evaluation gives $\mathbb P_1=(5/12,5/12,1/6)$ and $a(u)=5(1+\cos u)/24$, $b(u)=5(1-\cos u)/24$ in the two-time matrix. All six marginal residuals simplify to zero, and $[P_0,E_0]$ has entries $(0,1)=-1/2$, $(1,0)=1/2$, with all other entries zero.
- With the same Hamiltonian, bath and measurement, initial and first measurement time zero, second measurement time $u$, and symbolic initial diagonal entries $p_0,p_1,p_2$, the computed two-time matrix has upper block entries $(p_0+p_1)(1\pm\cos u)/4$, bottom diagonal entry $p_2$, and zero cross-block entries. This calculation is confined to that family; its extension to other measurement structures is not a computational result.
- At times $0,\pi/2,\pi$, with first and last outcome $0$, the three-time probabilities for middle outcomes $0,1,2$ are respectively $5/48,5/48,0$. Their sum is $5/24$, whereas $\mathbb P_2(0,\pi;0,0)=0$. Thus a three-time consistency violation is computed for this witness; it is not a theorem of the module.

**Argued, not formalized.**

- *Mechanism and a surviving sufficient construction.* The witness mixes only $\operatorname{span}\{e_0,e_1\}$; the remaining coordinate is a spectator. More generally, take a finite coordinate partition into nonempty blocks $B_\alpha$ of sizes $n_\alpha$, a rank-one orthonormal measurement supported separately in those blocks with squared overlaps $1/n_\alpha$ within each block, a diagonal density $\rho=\sum_jp_jE_j$, any finite-dimensional bath density $\sigma$, and Hermitian time-independent blocks $H_j$. For arbitrary $t_0\le t_1\le t_2$, the unmeasured joint state at $t_1$ is $\sum_jp_jE_j\otimes\sigma_j(t_1)$, where each $\sigma_j(t_1)$ is the unitary evolution of $\sigma$ under $H_j$ from $t_0$ and has trace one. The nonselective measurement maps each $E_j$ in $B_\alpha$ to $I_\alpha/n_\alpha$, so its joint output is $\sum_\alpha(I_\alpha/n_\alpha)\otimes A_\alpha$, with $A_\alpha=\sum_{j\in B_\alpha}p_j\sigma_j(t_1)$. Controlled unitary evolution to $t_2$ preserves the trace of every bath term. For any measurement outcome in $B_\alpha$, its probability at $t_2$ is therefore $\operatorname{Tr}(A_\alpha)/n_\alpha=(\sum_{j\in B_\alpha}p_j)/n_\alpha$, exactly its unmeasured one-time probability. Completeness of the final measurement gives the other marginal, and the block weights sum to one. This gives a direct argument for two-classicality under these hypotheses, without requiring global overlaps $1/d$ or a globally maximally mixed state. It does not by itself ensure time dependence; the fixed witness's `dependence` lemma supplies that property for the particular data in the Route.
- *Missing structure.* The noncommutation hypothesis is existential: it permits an incompatible block together with a fully compatible spectator. Excluding nontrivial common reducing projections of the energy and measurement PVMs excludes this block construction, but does not recover necessity of global unbiasedness: the stationary five-mode application below also satisfies that irreducibility condition. Merely assuming commuting bath Hamiltonians cannot exclude the displayed block witness, since $0,Z,2Z$ commute.
- *Nearby source results and consequences.* The source's Proposition `prop:2classicality_mubs` remains a sufficient construction for diagonal states measured in its phase-modified Fourier family; the refutation rejects its conjectured converse. The qubit necessity statement with a nonmaximally mixed diagonal state, nontrivial dephasing, and either Markovian dynamics or commuting $H_0,H_1$ (TeX lines 256–273) is not contradicted by a three-level example. Neither the maximally mixed-state proposition nor the Markovian sufficiency results use the conjectured converse as a premise. The compatible/MUB alternatives discussed in the conclusions (line 542) cannot furnish an exhaustive classification of two-classical protocols. The separate conjectures about full classicality in line 546 remain unsettled here: `result` concerns only two measurements, and the computed three-time violation prevents this witness from serving as an all-order-classical counterexample.

### Stationary five-mode application and the irreducibility boundary

The [owning Blueprint](../Blueprint/D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.md#a-stationary-five-mode-application-with-no-common-reducing-projection) gives the definitions, passive-frame correspondence and derivation for the original five-mode waiting/read matrix $K$ in mode order $(0,1,2,3,13)=(000,100,010,001,101)$. For every $\varepsilon>0$ with $5\varepsilon\lVert K\rVert_{\mathrm{op}}<1$, it uses $\rho_\varepsilon=I_5/5+\varepsilon K$, the Euclidean operator norm, nonnegative waits $e^{-itK}$, complete rank-one mode reads, finite outcome feedback and Stop. Its diagonal, nonuniform density spectrum is stationary in the passive simple-energy frame. With scalar bath $m=1$, bath state $[1]$, blocks $[\lambda_j]$ and measurement matrix $W^\dagger$, the literal joint laws are

$$
\mathbb P_1(x,t_1)=\frac15,\qquad
\mathbb P_2(y,t_2;x,t_1)=\frac{|U(t_2-t_1)_{yx}|^2}{5}.
$$

They satisfy normalization and both marginals for every ordered time pair and have actual time dependence. The two PVMs have only $0$ and $I$ as common orthogonal reducing projections, yet a zero-energy eigenvector has zero overlap with mode $000$, so the measurement is not mutually unbiased. Thus **this common-projector irreducibility condition does not repair the necessity implication**. This application does not assert that every stronger irreducibility condition fails.

The native all-finite-history supplier is `FiveModeRealResponse.five_mode_real_response_fiber`, transported by $D=\operatorname{diag}(1,i,i,i,1)$ with $D^\dagger K D=iA$. Every permitted complete-record law of $\rho_\varepsilon$ equals that of $I_5/5$. This is preparation aliasing, not measurement noninvasiveness: the native return experiment of *SelfGeneratedPredictiveMemory* §16 has first-branch weight $1/5$, conditional state $P_N$, and joint insertion gap $(p_B-p_A)/5>0$ for every sufficiently small positive $t$. Hence three-time consistency fails even though two-classicality holds.

This is an application of existing spectral, exponential, calculus and finite-history results, with no new exported Lean declaration and no change to `result : ¬ claim`. It assumes the complex density/Born/Lüders/coherent-waiting model. The scalar bath is a closed-system specialization; neither native acquisition of preparations and coherent controls nor a retained-environment extension follows. No new literature-priority or physical-realization claim is made.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The OpenAlex count and the Semantic Scholar screening are the attributed readings recorded in #21441, not independently reproduced citation searches. The screened records are arXiv:2601.06298, 2512.18873, 2408.03543, 2402.01218, 2310.10450, 2304.07110, 2211.04904 and DOI 10.1073/pnas.2520834123. The published APS versions of arXiv:2408.03543 and 2211.04904 were not read in that search because of HTTP 401. The reported arXiv version-history characterization and repository-wide absence search were not independently reproduced. The v2 TeX quotation and its surrounding definitions were read directly.

Everything under “Computed, not formalized” and “Argued, not formalized” beyond the explicitly named module lemmas is outside the Lean settlement. In particular, the original block witness's parameterized family calculation and three-time violation, the general blockwise construction, and the discussion of the source's remaining results have no additional formalization here. The stationary five-mode application likewise adds no exported Lean theorem. The common-projector irreducibility repair is excluded by the stationary five-mode application; stronger repairs, a classification of all two-classical measurements, and the source's distinct all-order conjectures remain open in this dossier. No physical implementation, experimental observation or unrestricted literature-priority claim is established.
