---
slug: chen-godsil-sobchuk-zhan-2024-bipartite-walk-reverse-state-transfer
bibkey: chenetal2024bipartitewalkhamiltonians
doi: 10.37236/12040
url: https://arxiv.org/abs/2207.01673v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.result
---

# No reverse perfect state transfer in the seven-state bipartite walk

## Problem

Q. Chen, C. Godsil, M. Sobchuk and H. Zhan, *Hamiltonians of bipartite walks*, arXiv:2207.01673v1; The Electronic Journal of Combinatorics 31(4) (2024), P4.10, Section “Open questions”, `Hamiltonian_7.tex`, line 1288:

> State $e_i$ is the characteristic vector of $i$. It is easy to see that there is perfect state transfer from state $e_1$ to $e_6$ at step $k=1$. But up to $k=300000$ steps, there is no perfect state transfer observed from $e_6$ to $e_1$. We suspect that there is no perfect state transfer from $e_6$ to $e_1$. We would like to find a condition on graph $G$ that determines whether or not perfect state transfer is symmetric.

The checked v1 TeX has md5 `2e3f9a1a91cb695794df49b0123dfc37`. Its evolution convention is $U^kz$ (lines 135–142), and its bipartite-walk definition is $U=(2P-I)(2Q-I)$ (lines 154–163). The projections for the seven-edge example are printed at lines 320–338, and its displayed transition matrix at lines 340–351 and 1278–1286. These definitions are documented in [the literature note](../Library/QuantumContext/chenetal2024bipartitewalkhamiltonians.md).

Use the source's one-based coordinate labels throughout this dossier. Let $U_{\rm def}=(2P-I)(2Q-I)$ for those explicit projections and let $U_{\rm disp}$ be the printed matrix. Exact rational comparison gives one discrepancy: their entries at row 3, column 5 are respectively $-1/3$ and $+1/3$; all other entries agree.

Issue [#21532](https://github.com/the-omega-institute/trureturing/issues/21532) fixes a reading covering both matrices. In Lean, `PerfectStateTransfer U a b` means that there exist $k\in\mathbb N$ and $\gamma\in\mathbb C$ with $\|\gamma\|=1$ and $U^ke_a=\gamma e_b$. The predicate imposes no unitarity assumption and includes step zero. The declaration `claim` says that neither $U_{\rm def}$ nor $U_{\rm disp}$ has such transfer from $e_6$ to $e_1$. This claim is proved by `result`.

## Motivation

The suspicion concerns an asymmetry between the two directions of exact state transfer, rather than the absence of transfer altogether. The source reports $Ue_1=e_6$ and a finite search for the reverse direction. An all-step obstruction would turn that observation into a concrete example distinguishing forward and reverse transfer. Covering both the reflection product and the printed matrix makes the answer independent of the sign discrepancy; the product is the matrix relevant to the defined bipartite quantum walk.

## Gap

The bounded literature check preregistered in #21532 records:

- direct reading of the v1 source and its explicit suspicion;
- a reported check that arXiv lists only v1 and that the 2024 journal version retains the suspicion;
- a reported reading of Chen, arXiv:2211.02752v3 (Phys. Scr., 2024), as establishing nonperiodicity without settling this reverse-transfer question, and inspection of two later citing papers;
- an OpenAlex count of five citing works for W4403097226;
- a repository search finding no settlement, with #11528 citing the source for its universal-state-transfer construction instead.

`not-found-in-searched-scope`. The present source reading reproduces the v1 quotation; the other literature and citation readings above are attributed to #21532 and are not independently reproduced here.

## Route

All coordinate labels below are one-based; the Lean indices are one less. For $s\in\mathbb Z$, let $M_s$ be the private integer matrix `M s`: multiply $U_{\rm disp}$ by 3 and replace its row-3, column-5 entry by $s$. Let $v=(-1,0,2,2,0,0,0)^{\mathsf T}$ and $w=(2,0,0,-2,2,-1,0)^{\mathsf T}$, the private definitions `v` and `w`. Write $(M_s)_{\mathbb C}$ for entrywise inclusion into complex matrices.

1. **Integer forms.** `integer_form_def` gives $3U_{\rm def}=(M_{-1})_{\mathbb C}$, and `integer_form_disp` gives $3U_{\rm disp}=(M_1)_{\mathbb C}$. For every $s\in\mathbb Z$ and complex $7\times7$ matrix $U$ satisfying $3U=(M_s)_{\mathbb C}$, `scaled_matrix` gives $U=\tfrac13(M_s)_{\mathbb C}$.
2. **Congruence invariant.** For every $s\in\mathbb Z$, `integer_first_column` gives $M_se_2=v$, and `integer_invariant` gives $M_sv=2v+3w$. For every such $s$ and every $n\in\mathbb N$, `orbit_mod` gives $M_s^nv\equiv2^nv\pmod3$ entrywise. Its proof uses the nonzero reduction of $v$ as an eigenvector with eigenvalue 2 in $\mathbb Z/3\mathbb Z$ and applies `Module.End.HasEigenvector.pow_apply`.
3. **Amplitude formula.** For every $s\in\mathbb Z$ and complex $7\times7$ matrix $U$ with $3U=(M_s)_{\mathbb C}$, `first_steps` gives $Ue_6=e_7$ and $Ue_7=e_2$. Under exactly that scaling hypothesis, for every $n\in\mathbb N$, `amplitude_formula` gives $(U^{n+3}e_6)_1=a_n/3^{n+1}$, where $a_n=(M_s^nv)_1\in\mathbb Z$. The congruence gives $a_n\equiv-2^n\not\equiv0\pmod3$.
4. **Norm obstruction.** For every $a\in\mathbb Z$ and $n\in\mathbb N$ with nonzero reduction of $a$ modulo 3, `fraction_ne_one` gives $\|a/3^{n+1}\|\ne1$ in $\mathbb C$. Norm one would imply $|a|=3^{n+1}$, so $3\mid a$, a contradiction.
5. **Transfer exclusion.** For every $s\in\mathbb Z$, complex $7\times7$ matrix $U$ with $3U=(M_s)_{\mathbb C}$, and $k\in\mathbb N$, `amplitude_ne_one` gives $\|(U^ke_6)_1\|\ne1$, handling $k=0,1,2$ by their zero first coordinate. For every $s,U$ satisfying the same scaling hypothesis, `no_transfer` excludes `PerfectStateTransfer U 5 0`: transfer would make that coordinate equal to a phase of norm one. `result` applies `no_transfer` to the two integer forms.

## Falsifier

A reversed coordinate convention, a change in the projections, or silently identifying the two printed matrix readings would invalidate the correspondence with the question. The Lean definitions `P`, `Q` and `Udisp` agree entrywise with the checked TeX matrices. `Udef` is their reflection product, and source coordinates 6 and 1 are exactly Lean indices 5 and 0. The direction follows the source's evolution $U^kz$ and its explicit example $Ue_1=e_6$.

The proof excludes the necessary condition $\|(U^ke_6)_1\|=1$ for transfer, so it also applies to the printed matrix without assuming it is unitary. It does not infer transfer from that scalar condition for a nonunitary matrix. Neither a finite absence of transfer nor nonperiodicity alone would settle the all-step statement; the integer congruence supplies the obstruction at every natural step.

## Evidence

The canonical source is `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.lean` (214 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.lean.json`, statement `sha256:0ee3790a81ff71b2a15acafade0d34cadbdfce78cd60f6da7f340aa74e0cecd7`.

Declaration statements:

- `result`: `sha256:7ca2230b801b54da65c8fcb7d1f90f5222f44f041f0e9d50216fceb1eb534990`;
- `claim`: `sha256:3628aea2c1b370059d312c4cddda1eb9be5aa3cbc62db439c55d9d86925c7164`.

## Triage

Tier 1: an explicit suspicion in a 2022 preprint published as a 2024 journal paper, preregistered in issue #21532 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for each of the two explicitly defined matrices $U_{\rm def}$ and $U_{\rm disp}$, there are no $k\in\mathbb N$ and $\gamma\in\mathbb C$ with $\|\gamma\|=1$ and $U^ke_6=\gamma e_1$.

**Computed, not formalized** (exact rational arithmetic on the TeX matrices; each item reproduced by the orchestrator with an independent script):

- The reflection product differs from the printed matrix only at row 3, column 5, with entries $-1/3$ and $+1/3$.
- $U_{\rm def}^{\mathsf T}U_{\rm def}=U_{\rm def}U_{\rm def}^{\mathsf T}=I$. The printed matrix is not orthogonal: the row-2, column-5 entry of $U_{\rm disp}^{\mathsf T}U_{\rm disp}$ is $4/9$.
- Both matrices send $e_1$ to $e_6$, $e_6$ to $e_7$, and $e_7$ to $e_2$. Their scaled matrices satisfy $M_se_2=v$ and $M_sv=2v+3w$ for the two tested values $s=-1,1$.
- For both tested matrices, a unit-modulus first coordinate of $U^ke_6$ was not observed for $0\le k\le60$. The congruence and amplitude formula were checked exactly for $0\le n\le57$. These finite checks supply no inference about untested steps.

**Argued, not formalized.**

- *Decisive structure and scope.* The interpretation of the private lemmas is arithmetic: `orbit_mod`, for every integer $s$ and natural $n$, preserves a nonzero first coordinate modulo 3, whereas `fraction_ne_one`, for integer numerator nonzero modulo 3 and positive denominator exponent $n+1$, excludes norm one. Thus the argument is independent of unitarity. Its algebraic scope is exactly that of `no_transfer`: integer $s$ and complex $7\times7$ matrix $U$ satisfying $3U=(M_s)_{\mathbb C}$. This explains robustness to the sign discrepancy. It supplies no graph realization or unitarity assertion for the other values of $s$, and no classification of arbitrary bipartite walks.
- *Exact versus approximate transfer.* For the real orthogonal matrix $U_{\rm def}$ checked above, compactness of the finite-dimensional unitary group supplies a convergent subsequence $U_{\rm def}^{n_j}\to V$, with indices chosen to have successive gaps $d_j=n_{j+1}-n_j\ge2$. Then $U_{\rm def}^{d_j}=U_{\rm def}^{n_{j+1}}(U_{\rm def}^{n_j})^{-1}\to I$. Using the computed identity $U_{\rm def}e_1=e_6$ gives $U_{\rm def}^{d_j-1}e_6=U_{\rm def}^{d_j}e_1\to e_1$ at positive steps. Thus an exclusion of exact reverse transfer need not give a positive uniform gap from unit amplitude. This compactness argument, its approximate-transfer conclusion and any recurrence-time bound are not formalized; no recurrence-time bound is supplied.
- *Effect on the source and neighbouring questions.* Combining the computed forward transfer for $U_{\rm def}$ with `result` gives the asymmetry anticipated in the quoted paragraph. In the checked v1 text, the suspicion occurs in the final “Open questions” section, without a theorem or corollary conditional on it; the settlement therefore supplies this example rather than changing a conditional theorem. The requested graph condition for symmetry remains open here. The separate question at TeX line 1290 asking for a graph with minimum degree at least three and perfect state transfer is also not settled. The source's Hamiltonian and universal-transfer constructions are not verified by this module.

## ASSUMED-UNVERIFIED

The literature check is bounded by the sources and citation readings recorded in #21532; it establishes neither exhaustive worldwide novelty nor priority. The journal text, the arXiv version listing, Chen arXiv:2211.02752v3, the two later citing papers, the OpenAlex citation count and the earlier repository-search result were not independently reproduced here. The source's reported search through 300000 steps was not reproduced; the independent exact scan covers only steps 0–60 for the two matrices.

The source-to-graph interpretation, orthogonality and forward-transfer calculations, the compactness argument and its approximate-transfer consequence, and the assessment of dependencies in the source are not additional conclusions of `result`. Matrix matching and the calculations above are external exact checks, not Lean declarations. The interpretations and deductions labelled “Argued, not formalized” have no additional formal theorem here. General graph criteria, the minimum-degree question and quantitative recurrence bounds remain open in this dossier.
