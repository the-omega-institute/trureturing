---
slug: zhao-pereira-ma-fei-2021-coherence-assistance-roof-equality
bibkey: zhaopereiramafei2021coherenceassistance
doi: 10.1038/s41598-021-85273-8
url: https://arxiv.org/abs/2103.08818v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.result
---

# A mixed four-dimensional state has equal coherence roofs

## Problem

M.-J. Zhao, R. Pereira, T. Ma and S.-M. Fei, *Coherence of assistance and assisted maximally coherent states*, Scientific Reports 11, 5935 (2021), arXiv:2103.08818v1, ask in the paragraph “Relation between the convex roof extension and the least concave majorant extension” (`ZhaoMJ-AMC4.tex`, line 303):

> The strict relation between the coherence of convex roof and the coherence of assistance, that is, whether $C_c(\rho)< C_a(\rho)$ holds for all mixed quantum states is an interesting topic.

The source's standing assumption is $f\in\mathfrak F\setminus\{0\}$ (lines 189–190): $f$ is real, symmetric and concave on the probability simplex and vanishes at its vertices. The pure-state coherence is $C_f(|\psi\rangle)=f(\mu(|\psi\rangle))$, where $\mu(|\psi\rangle)_i=|\psi_i|^2$ (lines 207–211).

In the formal reading, for every natural dimension $n$, `IsCoherenceFunction f` requires concavity on $\Omega_n=\{p\in\mathbb R^n:p_i\ge0,\ \sum_i p_i=1\}$, invariance under every coordinate permutation on $\Omega_n$, and $f(e_i)=0$ for every vertex. Nonzeroness means $\exists p\in\Omega_n,\ f(p)\ne0$.

A finite pure-state decomposition has nonnegative real weights $p_j$ summing to one, unit vectors $\psi_j\in\mathbb C^n$ for every index, and $\rho=\sum_jp_j|\psi_j\rangle\langle\psi_j|$. Let $D_f(\rho)$ be the set of all averages $\sum_jp_jf(\mu(\psi_j))$ over these decompositions. The module defines $C_c(\rho)=\inf D_f(\rho)$ and $C_a(\rho)=\sup D_f(\rho)$, using real `sInf` and `sSup`; the source uses minimum and maximum (lines 212–216 and 232–236). `IsMixed ρ` means $\rho\succeq0$, $\operatorname{tr}\rho=1$ and $\operatorname{tr}(\rho^2)\ne1$.

Issue [#22770](https://github.com/the-omega-institute/trureturing/issues/22770) fixes the claim: for every $n$, every such nonzero $f$, and every mixed $\rho$, $C_c(\rho)<C_a(\rho)$. This universal statement is refuted.

## Motivation

The question asks whether changing the pure-state ensemble with assistance always creates a strict increase over the convex roof, for every mixed state and every function in the source's class. The source connects this question to assisted coherence distillation (lines 303–306). Equal roofs distinguish a state with no ensemble-dependent gain for the chosen function from a universal assertion of strict gain; an operational distillation-rate statement requires its own correspondence to the chosen resource measure.

## Gap

Issue #22770 records the bounded literature check before any Lean:

- the 2021 source asks the question, and Zhao, L. Zhang and Fei, *Standard symmetrized variance with applications to coherence, uncertainty and entanglement* (2022), arXiv:2207.06048v1, restate the universal assertion as a conjecture;
- the oracle-reported searches of Zenodo, ResearchGate, SSRN and GitHub found no settlement, and the oracle-reported reading of Zhu, Zhang, An and Zeng (2025), arXiv:2406.19683, found that it does not address this question;
- the orchestrator's repository searches for both source identifiers and “coherence of assistance” found no prior matching dossier, Library note or D5 result; issue #20336 was recorded as unrelated.

`not-found-in-searched-scope`. The source passages are reproducible in the fetched TeX; the external search and prior repository-search readings remain attributed reports.

## Route

Use $f(p)=1-\sum_{i=0}^3p_i^2$, $\omega=(-1+\mathrm i\sqrt3)/2$, and

$v=(1/\sqrt2,1/\sqrt6,1/\sqrt6,1/\sqrt6)^{\mathsf T}$,
$w=(0,1/\sqrt3,\omega/\sqrt3,\omega^2/\sqrt3)^{\mathsf T}$.

Put $P=|v\rangle\langle v|+|w\rangle\langle w|$, $\rho_0=P/2$, and $S=\operatorname{span}_{\mathbb C}\{v,w\}$.

1. **Admissible function and state.** For this four-dimensional function, `quadratic_coherence` proves `IsCoherenceFunction f`, and `quadratic_nonzero` gives a nonzero simplex value. For these explicit vectors, `frame` proves both unit norms and both zero mutual inner products. `projection_properties` proves that $P$ is a self-adjoint idempotent and $\operatorname{tr}((I-P)\rho_0)=0$. `witness_mixed` proves exactly $\rho_0\succeq0$, $\operatorname{tr}\rho_0=1$ and $\operatorname{tr}(\rho_0^2)\ne1$.
2. **Constancy on the support.** For every $a,b\in\mathbb C$, with no normalization hypothesis, `fourth_moment` proves $\sum_i|av_i+bw_i|^4=(|a|^2+|b|^2)^2/3$. For $\psi\in\mathbb C^4$ satisfying both $\sum_i|\psi_i|^2=1$ and $(I-P)\psi=0$, `unit_span_value` proves $f(\mu(\psi))=2/3$.
3. **Every positive-weight component is supported there.** For arbitrary finite dimensions $n,k$, matrices $\rho,q$, weights $p$, vectors $\psi$, and an index $j$, `decomposition_support` assumes `IsDecomposition ρ k p ψ`, $q\succeq0$, $\operatorname{tr}(q\rho)=0$ and $p_j>0$, and concludes $q\psi_j=0$. Apply it with $q=I-P$ and $\rho=\rho_0$. The imported `AntidistinguishabilityGram.hermitian_projection_complement_psd` supplies $I-P\succeq0$ under its two hypotheses that $P$ is Hermitian and $P^2=P$; `projection_properties` supplies these. Components of weight zero contribute zero to the average without a support requirement.
4. **Attainment and equal roofs.** `witness_decomposition` proves the two-term decomposition of $\rho_0$ with weights $1/2,1/2$ and vectors $v,w$. `values_singleton` proves the exact set identity $D_f(\rho_0)=\{2/3\}$, including the existence of a decomposition attaining that value. Thus the set is nonempty and bounded on both sides, and `csInf_singleton` and `csSup_singleton` give $C_c(\rho_0)=C_a(\rho_0)=2/3$. `result` instantiates `claim` at this function and mixed state and contradicts strict inequality.

## Falsifier

The refutation would miss the question if it used an inadmissible function, a pure state, a restricted choice of ensembles, or an empty decomposition-value set. The definitions retain all finite decompositions, all nonnegative weights and unit vectors, the fixed reference basis, and the source's symmetric concave function class. The support argument applies to every positive-weight component of every such decomposition. The attaining decomposition and singleton identity also make the source's minimum and maximum coincide with the module's infimum and supremum at the witness; no general attainment theorem is needed for this counterexample.

## Evidence

The canonical source is `D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.lean.json`.

Declaration statements:

- `result`: `sha256:45cab6d5317fb5dae4fe76a1df59c5a85f83788283e33f10bdbd6859f7c094dd`;
- `claim`: `sha256:1a0f5eb709ae6e0d3c40d7e884d23d9d93f0694cc1ac2e832d184f45809341b7`.

## Triage

Tier 1 question of a 2021 paper, restated as a conjecture in the 2022 follow-up, preregistered in issue #22770 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural dimension, every symmetric concave real function on the probability simplex vanishing at every vertex and having a nonzero simplex value, and every positive semidefinite trace-one matrix whose square has trace different from one, the convex roof is strictly smaller than the coherence of assistance, both defined over all finite pure-state decompositions.

**Computed, not formalized:** a numerical sample of unit vectors in $S$ by the dossier seat found the coherence constant at $2/3$ to double precision.

**Argued, not formalized**.

- *Mechanism and rank.* For the explicit orthonormal pair certified by `frame`, $P$ projects onto the two-dimensional space $S$, so $\rho_0=P/2$ has rank two and is not full rank in $\mathbb C^4$. The constancy certified by `unit_span_value` requires a unit vector and $(I-P)\psi=0$; the universal support step requires every hypothesis of `decomposition_support` listed above. Consequently every allowed ensemble has the same average despite the state being mixed. Mixing alone does not force ensemble-dependent values.
- *Strict concavity does not repair the conjecture.* For distinct $p,r\in\Omega_4$ and $0<t<1$, direct expansion gives $f(tp+(1-t)r)-tf(p)-(1-t)f(r)=t(1-t)\sum_i(p_i-r_i)^2>0$. Thus this very function is strictly concave in the probability vector; that property does not prevent constancy on the coherence vectors arising from the unit sphere of $S$.
- *Surviving comparison and a sufficient condition.* If $D_f(\rho)$ is nonempty and bounded above and below, each $A\in D_f(\rho)$ satisfies $\inf D_f(\rho)\le A\le\sup D_f(\rho)$, so $C_c(\rho)\le C_a(\rho)$. Under these same boundedness assumptions, two finite decompositions with averages $A<B$ suffice for strictness, since $C_c(\rho)\le A<B\le C_a(\rho)$. The witness supplies no such pair.
- *The source's narrower results.* The 2021 source's Theorem `th ca=cc` (lines 314–317) states that, in a finite-dimensional Hilbert space, equality of the two roofs of a nonnegative pure-state function at a density matrix forces a positive semidefinite quadratic representation for every unit vector in that matrix's range. Here the constant value on $S$ has that representation with $Q=(2/3)I_S$. Corollary `cor coh` (lines 324–326) asserts strictness for full-rank states, which excludes $\rho_0$; neither source statement is contradicted by the counterexample. A characterization of all states or all functions with equal roofs remains open here.
- *Consequences for dependent assertions.* The conditional discussion at lines 303–306 of the 2021 source cannot establish strict assisted gain for every mixed state and every $f$ in its class once its universal premise is refuted. Zhao, Zhang and Fei (2022), arXiv:2207.06048v1, define $\widehat V(|\psi\rangle)=1-\sum_i|\psi_i|^4$ (`ZZ-2022-6.tex`, line 560), exactly the function used here. Following their qubit Theorem 5, lines 788–791 say: “This not only gives an affirmative answer to the conjecture that the concave bottom extension is strictly greater than the convex roof extension for all mixed states and all coherence measures”. Read with those unrestricted quantifiers, the assertion is refuted; a qubit-restricted conclusion does not imply it. This four-dimensional counterexample does not test the qubit-restricted theorem. Operational rates, the entropy-specific measure and the entanglement analogue are not settled by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check in #22770 does not establish exhaustive worldwide novelty or priority. The oracle-reported searches and reading of arXiv:2406.19683, and the orchestrator's prior repository-search readings, are not independently reproduced here. The TeX question and function definitions in arXiv:2103.08818v1 and the cited passages of arXiv:2207.06048v1 are checked directly; the journal versions and other cited papers are not independently read.

The numerical sample is not a proof for untested vectors. The additional arguments under “Argued, not formalized”, including strict concavity, rank, the general non-strict comparison and sufficient condition, and the discussion of consequences for the papers, are not conclusions stated by `result`. The general quadratic-representation theorem, full-rank corollary and qubit theorem are source statements, not formalized results of this module; their complete proofs are not independently certified here. No characterization of equality cases, minimal counterexample dimension, operational distillation-rate theorem or entanglement refutation is claimed.
