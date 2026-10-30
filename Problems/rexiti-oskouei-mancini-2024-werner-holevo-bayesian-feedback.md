---
slug: rexiti-oskouei-mancini-2024-werner-holevo-bayesian-feedback
bibkey: rexitioskoueimancini2024bayesianfeedback
doi: 10.1007/s11128-024-04467-x
url: https://arxiv.org/abs/2402.18941v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.result
---

# A strict Bayesian feedback advantage for the qutrit Werner–Holevo channel

## Problem

M. Rexiti, S. Khabbazi Oskouei and S. Mancini, *On the effectiveness of Bayesian discrete feedback for quantum information reclaiming*, arXiv:2402.18941v1, Quantum Information Processing 23, 258 (2024), Section 5, Conclusion, ask:

> There are a number of problems that this study poses in future perspective.
> First, find other examples of channels for which Bayesian feedback is more effective than Marokovian one.
> Then, for these channels see if by increasing the dimension the advantage increases.

This quotation is from the downloaded v1 source, `EffOfBayesianFB.tex`, lines 910–912, md5 `aeee6c3398ec2e49e99d0f461ed53290`; the spelling “Marokovian” is the source's. The [literature note](../Library/HilbertOperators/rexitioskoueimancini2024bayesianfeedback.md) gives the feedback definitions and source locators.

Issue [#23263](https://github.com/the-omega-institute/trureturing/issues/23263) specifies an answer to the first request using the qutrit Werner–Holevo channel
$\Phi(X)=\tfrac12(\operatorname{tr}(X)I_3-X^{\mathsf T})$.
For a finite family $K=(K_a)_{a\in\mathrm{Fin}\,m}$ of complex $3\times3$ matrices, `IsKrausDecomposition K` means
$\sum_a K_a X K_a^\dagger=\Phi(X)$ for every complex $3\times3$ matrix $X$.

The module specializes the source's two-step formulas in Section 2, lines 245–253, to dimension three:

$F_{\mathrm M}(K,L)=\tfrac19\sum_{a,b}\bigl(\operatorname{Re}\operatorname{tr}(|L_b|\,|K_a|)\bigr)^2$,

$F_{\mathrm B}(K,L)=\tfrac19\sum_{a,b}\|L_b|K_a|\|_1^2$,

where $|T|=\sqrt{T^\dagger T}$ and $\|M\|_1=\operatorname{Re}\operatorname{tr}\sqrt{M^\dagger M}$.
The settled statement is that every pair of finite Kraus decompositions has $F_{\mathrm M}\le\tfrac12$, while some pair of three-operator Kraus decompositions has $F_{\mathrm B}>\tfrac12$.

## Motivation

The comparison concerns recovery of entanglement fidelity through measurements of the environment and outcome-dependent corrections. A Bayesian witness exceeding a universal Markovian bound demonstrates an advantage even when the Markovian measurements can be chosen freely at both steps.

Rexiti, Oskouei and Mancini (2024), arXiv:2402.18941v1, introduce their qutrit examples in Section 4, lines 677–679:

> In this Section we consider two enlightening examples of channels
> ${\cal T}:{\mathfrak{S}}(\mathbb{C}^3)\to {\mathfrak{S}}(\mathbb{C}^3)$.
> The first one (dephasing channel) for which Bayesian feedback does not offer any advantage over the Markovian feedback, and the second one (amplitude damping) which instead does.

The Werner–Holevo example supplies another channel for the requested comparison. Its distinction from the source's amplitude damping family is explained below by a direct unitality calculation, separately from the formal statement.

## Gap

The bounded literature check recorded in #23263 attributes the following findings to the orchestrator:

- Semantic Scholar listed no citing work of arXiv:2402.18941.
- arXiv searches for “Bayesian feedback” with “Mancini”, and for Rexiti, found later channel-discrimination work but no further information-reclaiming example.
- Repository issue and text searches found only the different channel-discrimination problem #16535.

The issue also records oracle-reported searches of Zenodo, ResearchGate, SSRN and GitHub, with no settlement found; those searches were not repeated by the orchestrator. These are attributed search findings, not an exhaustive novelty determination.

`not-found-in-searched-scope`.

## Route

All lemma names below refer to `WernerHolevoBayesianFeedbackAdvantage`. Write $A(z)$ for the matrix of $y\mapsto z\times y$ on $\mathbb C^3$ and $z^\dagger w$ for the Hermitian inner product.

1. **Represent every admissible finite family.** For every $m\in\mathbb N$ and $K:\mathrm{Fin}\,m\to M_3(\mathbb C)$ satisfying `IsKrausDecomposition K`, `kraus_classification` gives vectors $z_a\in\mathbb C^3$ such that $K_a=A(z_a)/\sqrt2$ and $\sum_a z_a z_a^\dagger=I_3$. This applies to all such finite families, including families containing zero operators.
2. **Control the absolute values and pair traces.** For every $z\in\mathbb C^3$, `abs_crossProduct` gives zero when $z=0$ and, when $z\ne0$, gives $|A(z)/\sqrt2|=(\|z\|I_3-\|z\|^{-1}zz^\dagger)/\sqrt2$. For every $w,z\in\mathbb C^3$, with no nonzero hypothesis, `abs_pair_bound` gives
   $\bigl(\operatorname{Re}\operatorname{tr}(|A(w)/\sqrt2|\,|A(z)/\sqrt2|)\bigr)^2\le\tfrac14(\|w\|^2\|z\|^2+3|w^\dagger z|^2)$.
3. **Sum using both frame identities.** For any finite vector family $z$ satisfying $\sum_a z_a z_a^\dagger=I_3$, `frame_q_sum` gives $\sum_a\|z_a\|^2=3$. For any two finite vector families $z,w$ each satisfying that identity, `frame_inner_sum` gives $\sum_{a,b}|w_b^\dagger z_a|^2=3$. Thus the double sum of products of squared norms is $9$, and the pair bound sums to $(9+3\cdot3)/36=\tfrac12$. The lemma `markov_bound` states this bound for every pair of finite matrix families satisfying both `IsKrausDecomposition` hypotheses.
4. **Exhibit a strictly better Bayesian pair.** The fixed families are $K_i=A(e_i)/\sqrt2$ and $L_j=A(w_j)/\sqrt2$, indexed by $\mathrm{Fin}\,3$, with $w_0=(2,2,-1)/3$, $w_1=(-1,2,2)/3$ and $w_2=(2,-1,2)/3$. The lemmas `canonical_is_kraus` and `rotation_is_kraus` certify these particular families without additional hypotheses. For every $i,j\in\mathrm{Fin}\,3$, `bayes_pair_trace` gives $\operatorname{Re}\operatorname{tr}\bigl|L_j\,|K_i|\bigr|=(1+|\operatorname{Re}(w_j)_i|)/2$. The proof of `bayesian_witness` evaluates the resulting fidelity to $11/18$; the lemma's declared conclusion is $\tfrac12<F_{\mathrm B}(K,L)$. The theorem `result` combines this existential witness with the universal Markovian bound.

## Falsifier

A valid finite Kraus pair with $F_{\mathrm M}>\tfrac12$ would contradict the universal conjunct. The witness route requires both operator-sum identities on every matrix and the strict Bayesian inequality for the specified pair; comparing it only with a selected Markovian measurement would not establish the universal comparison.

The fidelity definitions agree with the source's two-step formulas, with the real trace written explicitly and the trace norm defined by the positive square root. Each step uses a fixed Kraus decomposition, which may differ between the two steps. The second decomposition is not indexed by the first outcome; the Bayesian correction uses the accumulated branch. The formal statement concerns these finite decompositions in dimension three and two channel uses.

## Evidence

The canonical source is `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.lean`.

- **Proof.** `result` proves the conjunction of the universal Markovian bound and the existence of two three-operator Kraus decompositions with Bayesian fidelity strictly above $\tfrac12$.
- **Axioms.** `#print axioms` on `result` gives only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.lean.json`.

Declaration statements:

- `result`: `sha256:8daaa0fb2a393258d56cea19633fee4ad61a464f0742f4c99da2c970fce72cea`.

## Triage

Tier 1 explicit open request of a 2024 Quantum Information Processing paper, preregistered in issue #23263 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $m_1,m_2\in\mathbb N$ and every pair $K:\mathrm{Fin}\,m_1\to M_3(\mathbb C)$, $L:\mathrm{Fin}\,m_2\to M_3(\mathbb C)$, if both are Kraus decompositions of $\Phi$ on every complex matrix, then $F_{\mathrm M}(K,L)\le\tfrac12$; and there exist $K,L:\mathrm{Fin}\,3\to M_3(\mathbb C)$, both Kraus decompositions of $\Phi$, with $F_{\mathrm B}(K,L)>\tfrac12$.

**Computed, not formalized:** a floating-point evaluation by the dossier seat agrees with the formal statement: the canonical pair gives both fidelities $1/2$, the canonical/rational-rotation pair gives Bayesian fidelity $11/18$, and the canonical/Fourier pair of #23263 gives Bayesian fidelity $(2+\sqrt3)/6$.

**Argued, not formalized**:

- *Sharpness of the Markovian bound.* For each $i\in\mathrm{Fin}\,3$, `abs_canonical` gives $|K_i|=(I_3-e_i e_i^\dagger)/\sqrt2$. Therefore $\operatorname{tr}(|K_j|\,|K_i|)=1$ when $i=j$ and $1/2$ otherwise. The canonical pair has $F_{\mathrm M}=(3+6/4)/9=\tfrac12$. Together with the universal bound this gives attainment of the Markovian optimum by direct matrix algebra; attainment and a supremum equality are not conclusions stated by `result`.
- *Mechanism and the commuting boundary.* The representation in `kraus_classification`, under its finite Kraus-decomposition hypothesis, and the nonzero branch of `abs_crossProduct` identify the absolute values as scaled orthogonal-complement projections. Changing the frame changes their relative directions. For the chosen unit vectors, $0<|e_i^\dagger w_j|<1$, so the corresponding rank-one projections do not commute: their ranges are neither equal nor orthogonal. In contrast, if every $|K_a|$ commutes with every $|L_b|$ for an arbitrary finite pair, $B=|L_b|\,|K_a|$ is positive semidefinite and $(L_b|K_a|)^\dagger(L_b|K_a|)=B^2$. Uniqueness of the positive square root gives $\bigl|L_b\,|K_a|\bigr|=B$, hence the two fidelities coincide. This explains the commuting case without asserting that noncommutation alone guarantees an advantage.
- *A channel beyond the source's damping family.* Substitution gives $\Phi(I_3)=I_3$. For the qutrit amplitude damping family with $p\in[0,1]$ in Rexiti, Oskouei and Mancini (2024), arXiv:2402.18941v1, Section 4.2, the displayed Kraus operators give $(\mathcal A_p(I_3))_{22}=(1-p)^2$. Unitality would force $p=0$, where $\mathcal A_p$ is the identity. But $\Phi(e_0e_0^\dagger)=(I_3-e_0e_0^\dagger)/2$ is not $e_0e_0^\dagger$. Thus this example is distinct from every member of that family.
- *Scope and neighbouring questions.* The universal bound already allows arbitrary finite cardinalities, complex operators and zero operators; its hypotheses require both families to represent this particular channel. The exact optimal Bayesian value, higher-dimensional analogues, more than two feedback steps and history-dependent choices of environmental measurements remain open in this settlement. The Fourier calculation above is a tested witness value, not a formal optimum.
- *Effect on the source.* This supplies an example for the first request in the conclusion. The source's qubit conjecture in Section 3 and its dephasing and amplitude damping analyses in Section 4 do not depend on a solution to that request; their conclusions acquire no additional verification from this module. The separate requests about increasing dimension and the continuum limit remain unsettled.

## ASSUMED-UNVERIFIED

The bounded literature check in #23263 does not establish exhaustive worldwide novelty or priority. Its Semantic Scholar listing, arXiv author searches, readings of later discrimination papers and repository-wide search findings are attributed to the orchestrator and were not independently reproduced here. The oracle's Zenodo, ResearchGate, SSRN and GitHub searches are likewise unverified.

The numerical calculations listed above are finite floating-point checks. The orchestrator's 3000 random-pair experiment recorded in #23263 was not reproduced. The source's numerical studies of other channels were read but not rerun. No conclusion about untested families follows from those numerical checks.

The arguments labelled “Argued, not formalized” are not additional Lean conclusions. The local rational-witness evaluation inside `bayesian_witness` is part of its proof, but `result` states only the strict existential inequality. The module defines no supremum quantity, and `result` contains no attainment assertion. The exact Bayesian optimum, extensions to other dimensions or numbers of steps, the continuum limit and history-dependent environmental measurements have no formal settlement here. The oracle-reported multistep formulas mentioned in #23263 are unverified and are not adopted as conclusions.
