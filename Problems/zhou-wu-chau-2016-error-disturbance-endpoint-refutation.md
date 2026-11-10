---
slug: zhou-wu-chau-2016-error-disturbance-endpoint-refutation
bibkey: zhouwuchau2016errordisturbance
doi: 10.1016/j.physleta.2016.03.046
url: https://arxiv.org/abs/1509.03812v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.result
---

# The Zhou–Wu–Chau endpoint lower bound on overall error is false

## Problem

S. S. Zhou, S. Wu and H. F. Chau, *State-Independent Error-Disturbance Tradeoff For Measurement Operators*, arXiv:1509.03812v1 (2015), published as *State-independent error-disturbance trade-off for measurement operators*, Physics Letters A 380(22–23), 1918–1924 (2016), DOI 10.1016/j.physleta.2016.03.046, state Conjecture 3 in Section IV. The v1 source `new_912arxiv.tex`, lines 625–638, reads:

> For all $d \geq 2$, the following trade-off between error and disturbance holds: $\varepsilon(\mathcal{A},\mathcal{A}') + \eta(\mathcal{A}',\mathcal{B}) \geq f(\mathcal{A},\mathcal{B})$ and $\Delta(\mathcal{A},\mathcal{A}',\mathcal{B}) \geq f(\mathcal{A},\mathcal{B})$, where $f(\mathcal{A},\mathcal{B}) = \min \{ \varepsilon(\mathcal{A},\mathcal{B}),\eta(\mathcal{A},\mathcal{B}) \}$. Moreover, the equalities are both attained either when for all $i$, $\ket{a'_i} = \ket{a_i}$, or when for all $i$, $\ket{a'_i} = \ket{b_i}$.

The source uses rank-one projective measurements associated with orthonormal bases of $\mathbb C^d$. Section II defines the outcome-distance by $D(x,y)=\max_i|x_i-y_i|$ and compares the $\mathcal B$ statistics before and after the nonselective $\mathcal A'$ measurement. Its overall quantity is explicitly

> $\Delta(\mathcal{A}, \mathcal{A}', \mathcal{B}) = \max_\rho \left( \varepsilon_{\rho}(  \mathcal{A}, \mathcal{A}') + \eta_{\rho}(  \mathcal{A}', \mathcal{B})\right).$

This is line 221 of the source. Both terms use one common density matrix. Immediately before the conjecture, lines 616–620 relax the endpoint error by

> $\varepsilon(\mathcal{A},\mathcal{B}) = \min_{\tilde{\mathcal B}} \varepsilon(\mathcal{A},\tilde{\mathcal{B}})$,

with the explanation

> This relaxed definition of $\varepsilon$ means that we only distinguish between the classical probability distributions resulting from measurements $\mathcal{A}$ and $\mathcal{B}$ with no regard to the labeling of different measurement outcomes.

The definitions and source locator are collected in [the literature note](../Library/Estimation/zhouwuchau2016errordisturbance.md).

Issue [#23208](https://github.com/the-omega-institute/trureturing/issues/23208) fixes the statement: for every natural $d\ge2$ and all three unitary measurement bases $A,A',B$, the minimum of the endpoint error, minimized over outcome permutations, and the disturbance caused by $A$ is at most $\Delta(A,A',B)$. This second inequality is refuted. The first inequality, concerning the sum of two separately maximized quantities, is not settled here.

## Motivation

The proposed bound would identify the best endpoint cost as a universal lower bound on error plus disturbance evaluated in a common state. It would justify choosing an endpoint measurement rather than accepting some error to reduce disturbance. The distinction between a common-state maximum and the sum of separate maxima matters: a lower bound on the latter does not supply the proposed lower bound on the former.

## Gap

Issue #23208 records the orchestrator's bounded literature check before any Lean: the Semantic Scholar citation listing and its listed citing text, arXiv API searches, Zenodo, the issues of `Naixu-Guo/quantum-open-problems`, and repository issue and text searches yielded no settlement in the searched scope. Additional searches of ResearchGate, SSRN, GitHub and Zenodo were reported by GPT Pro and were not independently repeated by the orchestrator. These search readings are attributed to the issue; they are not independently reproduced here.

`not-found-in-searched-scope`.

## Route

Use zero-based outcome indices $0,1,2$. The standard basis is $A=I$, and $A'$ and $B$ are the columns of

$U=\frac1{313}\begin{pmatrix}312&-25&0\\25&312&0\\0&0&313\end{pmatrix}$,
$V=\frac1{33205}\begin{pmatrix}32976&-3757&-1020\\3893&31824&8640\\0&-8700&32045\end{pmatrix}$.

The private lemmas `u_unitary` and `v_unitary` verify these fixed matrices are unitary. Write $P_i,Q_i,R_j$ for the column projectors of $I,U,V$, and set $E_i=P_i-Q_i$ and $D_j=R_j-\sum_kQ_kR_jQ_k$. Put $s=71/250$ and $r=57/200$.

1. **Signed certificates.** For this fixed triple, `signed_certificate` proves $sI-(\epsilon E_i+\delta D_j)$ is positive semidefinite for every $i,j\in\mathrm{Fin}\,3$ and every real $\epsilon,\delta$ satisfying $\epsilon=1$ or $\epsilon=-1$, and $\delta=1$ or $\delta=-1$. The twelve cases at $i=0$ come from `first_signed_certificate`, whose parameters are $j\in\mathrm{Fin}\,3$ and two Boolean sign selectors. Each uses `psd_of_ldl`: for complex $3\times3$ matrices $H,L$ and a real vector $q:\mathrm{Fin}\,3\to\mathbb R$, if every $q_k\ge0$ and $H=L\operatorname{diag}(q)L^*$, then $H$ is positive semidefinite. The tables `e_table` and `f_table` give the entries for each index in $\mathrm{Fin}\,3$; in particular $E_1=-E_0$ and $E_2=0$. The zero case follows by averaging the two certificates with opposite $E_0$ signs.
2. **One common state.** For any complex $3\times3$ density matrix $\rho$, indices $i,j\in\mathrm{Fin}\,3$ and real signs $\epsilon,\delta\in\{1,-1\}$, `signed_expectation` gives $\epsilon\operatorname{Re}\operatorname{tr}(\rho E_i)+\delta\operatorname{Re}\operatorname{tr}(\rho D_j)\le s$. Taking maximizing outcome indices and the signs of their expectations, `state_overall_bound` gives $\varepsilon_\rho(I,U)+\eta_\rho(U,V)\le s$ for every such density matrix. The set of density matrices in dimension three is nonempty, by `CartesianVariance.density_nonempty` with its hypothesis $0<3$. Thus `overall_bound` takes the supremum over a nonempty set with this uniform upper bound and gives $\Delta(I,U,V)\le s$.
3. **Legitimate endpoint suprema.** For any natural dimension $d$ and complex $d\times d$ matrices $\rho,X,Y$, `effect_difference_bound` assumes $\rho$ is positive semidefinite of trace one and that $X,Y,I-X,I-Y$ are all positive semidefinite; it concludes $|\operatorname{Re}\operatorname{tr}(\rho(X-Y))|\le1$. For the fixed $B=V$ and every $j\in\mathrm{Fin}\,3$, `standard_pinch` identifies measurement in $I$ with taking the diagonal of $R_j$. These facts give `disturbance_bdd` for the fixed pair $(I,V)$ and `error_bdd` for every permutation $\pi$ of $\mathrm{Fin}\,3$: each set of state-dependent values defining the corresponding endpoint supremum is bounded above by one.
4. **Endpoint witnesses.** The helper `pure_isDensity` applies to $x:\mathrm{Fin}\,3\to\mathbb C$ and real $n$ under both $n>0$ and $\sum_k x_k\overline{x_k}=n$, and proves $xx^*/n$ is a density matrix. Using $x=(-5,11,-10)$ and $n=246$, `disturbance_witness` supplies a density matrix whose disturbance for $(I,V)$ exceeds $r$. For every permutation $\pi$ of $\mathrm{Fin}\,3$, `error_witness` supplies a density matrix whose labeled error for $(I,V\circ\pi)$ exceeds $r$: it uses $x=(-5,-16,-11)$, $n=402$ when $\pi(1)=1$, and $x=(0,1,0)$, $n=1$ when $\pi(1)=0$ or $2$. The boundedness lemmas justify passing these witnesses to the real suprema in `disturbance_lower` and `relaxed_lower`; finiteness and nonemptiness of the permutation type justify the strict lower bound on its infimum.
5. **Contradiction.** For this triple the endpoint minimum is strictly above $r$, whereas $\Delta(I,U,V)\le s<r$. The theorem `result` contradicts `claim` at $d=3$.

## Falsifier

The settlement would miss the source if it changed the state space, discarded the common-state constraint, or omitted an allowed outcome relabeling. The module uses positive semidefinite complex matrices of trace one (`IsDensity`), rank-one projectors onto columns of unitary matrices (`measurementProjector`), and the nonselective channel $X\mapsto\sum_kQ_kXQ_k$ (`unreadState`). The real trace expectations in `errorAt` and `disturbanceAt` give the source's infinity distances on density matrices; cyclicity of trace moves this channel between states and observables. The definitions `error`, `disturbance` and `overallError` take real suprema over these density matrices, and `relaxedError` takes the infimum over every outcome permutation. The route establishes the nonemptiness and bounds needed at the counterexample, rather than relying on values of unbounded or empty real suprema.

The formal reading relaxes the endpoint error in the right-hand side and keeps the labels in the common-state quantity fixed. Minimizing the intermediate labels as well can only reduce that quantity, since the identity relabeling remains available. Conversely, using the unrelaxed endpoint error can only increase the right-hand side. Thus neither alternative reading repairs this counterexample; these comparisons are arguments from the definitions, not additional declarations of `result`.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:25c15783b282660d9bebecef6ba607aad982cf68d47b567c78e4f0e8502b4c5c`;
- `claim`: `sha256:4b2d92a744da502c82f0b10aed2e1c3cab2fbe6b8e2eace969b6ce457f13216f`.

## Triage

Tier 1 conjecture of a 2015 preprint associated with a 2016 journal publication, preregistered in issue #23208 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural $d\ge2$ and all unitary measurement bases $A,A',B$ of $\mathbb C^d$, $\min\{\varepsilon_{\mathrm{rel}}(A,B),\eta(A,B)\}\le\Delta(A,A',B)$, where $\varepsilon_{\mathrm{rel}}$ is the minimum over outcome permutations of the labeled error suprema, $\eta$ is the disturbance supremum, and $\Delta$ is the supremum of the error-plus-disturbance sum in one common density matrix.

**Computed, not formalized:** for the fixed qutrit triple, a floating-point evaluation by the dossier seat places the overall error about $0.0016$ below the endpoint minimum, gives overall errors at the two endpoints $A'=A$ and $A'=B$ that agree, to the computed precision, with $\eta(A,B)$ and $\varepsilon_{\rm rel}(A,B)$ respectively, and finds the first inequality of the conjecture satisfied at this instance.

**Argued, not formalized.**

- *Mechanism and a sufficient extra condition.* For any fixed finite dimension $d\ge2$ and unitary triple, the identity $\max_i|x_i|+\max_j|y_j|=\max_{i,j,\epsilon,\delta\in\{1,-1\}}(\epsilon x_i+\delta y_j)$ and maximization of a Hermitian expectation over density matrices give $\Delta=\max_{i,j}\max\{\|E_i+D_j\|,\|E_i-D_j\|\}$, where $E_i=P_i-Q_i$ and $D_j=R_j-\sum_kQ_kR_jQ_k$ refer to that triple and the norm is the operator norm. Indeed, the finite maximum commutes with the supremum over states, and each signed Hermitian expectation is maximized by a top eigenvector. The same argument gives $\varepsilon(A,A')=\max_i\|E_i\|$ and $\eta(A',B)=\max_j\|D_j\|$. Separately optimized error and disturbance lose the constraint that the same state realizes both. If the first inequality holds for a triple and one density matrix attains both separate maxima, then that state makes $\Delta=\varepsilon+\eta\ge f$; this is a sufficient extra condition, not an assertion that such a state always exists.
- *Endpoint optimality.* At $A'=A$ the error is zero, so $\Delta=\eta(A,B)$. At $A'=B\circ\pi$ the disturbance is zero, because the nonselective measurement fixes every $B$ projector, so $\Delta=\varepsilon(A,B\circ\pi)$. Minimizing over the finitely many permutations gives the other endpoint cost $\varepsilon_{\mathrm{rel}}(A,B)$. The strict separation in the route therefore puts an intermediate measurement below both endpoint costs, including the best labeling of the second endpoint.
- *Stability in dimension three.* The preceding finite spectral formulas express error, disturbance and overall error as finite maxima of continuous functions of the unitary entries; relaxed error is a finite minimum of these continuous functions. Their strict gap at the fixed triple therefore persists on an open neighbourhood in $U(3)^3$. No quantitative neighbourhood radius is supplied.
- *Embedding in every dimension $d\ge3$.* Pad $I,U,V$ by the same identity block. Every nonzero error or disturbance observable is supported on the original three-dimensional block. A density matrix has a positive semidefinite compression to that block of trace $t\in[0,1]$; for $t>0$ normalization gives a qutrit density matrix and scales both state-dependent quantities by $t$, while $t=0$ gives zero. States supported on the block recover every qutrit value, so the overall error and endpoint disturbance are unchanged. An outcome permutation moving a core column to an added coordinate or moving any added column from its matching coordinate has labeled error one, witnessed by a standard basis state. Every remaining permutation fixes all added coordinates and restricts to a core permutation, whose error is the qutrit error by the same compression argument. Since all labeled errors are at most one and a core-preserving permutation is available, the relaxed endpoint error is unchanged as well. Thus the strict separation extends to these padded triples.
- *Restricted statements and unresolved strength.* The source's Theorem 1 assumes $d=2$ and states “$\Delta(\mathcal{A},\mathcal{A}',\mathcal{B}) \geq \eta(\mathcal{A},\mathcal{B})$” (line 464). Its Theorem 2 assumes mutually unbiased $A,B$ for all $d\ge2$ and states “$\varepsilon(\mathcal{A},\mathcal{A}') + \eta(\mathcal{A}',\mathcal{B}) \geq \eta(\mathcal{A},\mathcal{B}) = 1 - 1/d$” (line 556); that theorem's displayed statement does not assert a bound on $\Delta$. The witness is three-dimensional and its $A,B$ have a zero overlap, so they are not mutually unbiased. It does not refute either restricted statement. The first inequality in Conjecture 3 for arbitrary unitary triples remains unsettled here.
- *Effect on the paper.* Immediately after Conjecture 3 the source says, “If our conjecture can be proved, the validity of our trade-off relation will be extended to any operator in Hilbert space” (line 641), followed by “Our sharp lower bound $f(\mathcal{A},\mathcal{B})$ will then serve as a importance physical quantity characterizing the trade-off between error and disturbance in consecutive measurement process” (line 642). The common-state inequality cannot support this proposed extension: $f$ is not a universal lower bound on $\Delta$. The counterexample does not invalidate the source's separately stated qubit theorem or its mutually unbiased sum bound, and it does not settle whether $f$ remains a universal lower bound on the sum of separate maxima.

## ASSUMED-UNVERIFIED

The bounded literature check is the orchestrator's reading recorded in #23208, including its account of the listed citing work, rather than an independently reproduced search or citing-paper reading. GPT Pro's additional search reports were not independently reproduced. These bounds on the search do not establish exhaustive worldwide novelty or priority. The journal text was not read; agreement of its conjecture with arXiv:1509.03812v1 is unverified.

The source reading is the v1 e-print member `new_912arxiv.tex`, md5 `224f302edfcd0f7e887b2c9695c86591`, including the definitions in Section II and the statements, conjecture and conclusion in Section IV and Section V. The source's special-case theorem statements were read, but their proofs are not independently certified here. Compactness and trace-cyclicity arguments identifying the source's maxima and state channel with the module's suprema and observable channel are not additional formal declarations in this module.

The statements in “Computed, not formalized” and “Argued, not formalized,” including the spectral interpretation, endpoint identities, alternative labeling readings, neighbourhood stability and higher-dimensional embedding, are not formalized by `result`. The decimal values are numerical evaluations for the fixed triple only. No universal result on the conjecture's first inequality, no optimal replacement lower bound and no quantitative stability radius is established here.
