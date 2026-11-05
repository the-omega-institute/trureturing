---
slug: jiang-klco-di-matteo-2025-cartesian-control-angle-matrix-invertibility
bibkey: jiangklcodimatteo2025cube
doi: 10.1103/rrmd-fqx6
url: https://arxiv.org/abs/2506.10945v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.result
---

# Cartesian-control angle matrices are invertible for mixed qudit dimensions

## Problem

J. Jiang, N. Klco and O. Di Matteo, *Non-Abelian dynamics on a cube: Improving quantum compilation through qudit-based simulations*, arXiv:2506.10945v1 (Phys. Rev. D 112, 074512, 2025), state the following conjecture in `subsec_3c_restricted-rotations.tex`, lines 38–46 (the display labelled `eq:conjecture`). The quotation expands the source macro `\ctrlseq` as $\boldsymbol C$ and renders its displayed equation inline:

> By keeping $\boldsymbol C$ general, we sacrifice the guarantee that the matrix $M$ is invertible, although we conjecture our particular implementation yields an invertible $M$ when $\{\boldsymbol C\} = \mathbb{Z}_{d_1} \times \mathbb{Z}_{d_2} \times \cdots \times \mathbb{Z}_{d_k}$, i.e., uniform control but non-uniform qudit dimension.

Equation (5), `subsec_3a_uniform-rotations.tex`, lines 38–49, defines $\boldsymbol\theta=M\boldsymbol\beta$ and $M_{ij}=\prod_l(-1)^{f(b_l^{(i)},g_l^{(j)})}$, where $f(b,g)=1$ when $0<b\le g$ and $f(b,g)=0$ otherwise. Here $b$ and $g$ are control-word sequences. The definitions and source locators are collected in [the literature note](../Library/Eigenstructure/jiangklcodimatteo2025cube.md).

Issue [#23818](https://github.com/the-omega-institute/trureturing/issues/23818) fixes the reading as invertibility for every pair of enumerations of the full Cartesian control set. Precisely, for every $k\in\mathbb N$, every $d:\mathrm{Fin}\,k\to\mathbb N$, and every pair of bijections $b,g:\mathrm{Fin}\,N\simeq C$, where $N=\prod_l d_l$ and $C=\prod_{l:\mathrm{Fin}\,k}\mathrm{Fin}(d_l)$, `angleMatrix d b g` is the real matrix with entries
$M_{ij}=\prod_l\bigl(\text{if }0<b(i)_l\le g(j)_l\text{ then }-1\text{ else }1\bigr)$.
The proposition `claim` says that this matrix is a unit in the real square-matrix ring, so it has a two-sided inverse; `result : claim` proves it. There is no lower-bound hypothesis on the dimensions.

## Motivation

The matrix converts desired controlled-rotation angles into the angles of the decomposed circuit. Invertibility removes the linear-algebra obstruction to realizing any prescribed real angle vector. Mixed dimensions occur when different control qudits have different allowed level ranges. The conjecture asks whether the source's sequencing construction retains this property on the full product of those ranges.

## Gap

The bounded literature check in #23818 records:

- the conjecture in arXiv:2506.10945v1 and an arXiv listing with only v1;
- 21 INSPIRE citing records, with 19 citing arXiv sources checked by the orchestrator: no occurrence of `invertib`, and the sole `conjectur` hit concerns counterterms;
- search-agent reports of no settlement in searches of Zenodo, ResearchGate, SSRN, GitHub and the authors' `QSAR-UBC/QuditOpsViaLGT` repository;
- no prior repository issue found by the orchestrator's searches for the arXiv identifier, Di Matteo and Klco.

`not-found-in-searched-scope`. Retention of the conjecture in the journal text is unverified.

## Route

1. **One coordinate.** For every natural $m$, the private definition `A m` is the real matrix on $\mathrm{Fin}\,m$ with entry $-1$ exactly when $0<r\le s$, and $1$ otherwise. The private definition `E m` keeps row zero and replaces every positive row $r$ by half of row zero minus half of row $r$. For every $m$, `E_mul_A` proves $E_mA_m=Z_m$, where $Z_m(r,s)=1$ for $r\le s$ and $0$ otherwise, the zeta matrix of $\mathrm{Fin}\,m$. For every $m$, `det_zeta` proves $\det Z_m=1$ using upper triangularity and its unit diagonal; `det_A_isUnit` takes determinants of the product to prove that $\det A_m$ is a unit. These lemmas require no positivity hypothesis; at $m=0$ the matrix identities and diagonal product are empty.
2. **The Cartesian product.** For every natural $k$ and every $d:\mathrm{Fin}\,k\to\mathbb N$, the private definitions `K d` and `LinvPrime d` have entries $K(r,s)=\prod_l A_{d_l}(r_l,s_l)$ and $L(r,s)=\prod_l(A_{d_l}^{-1})(r_l,s_l)$. Under exactly these parameters, `LinvPrime_mul_K` proves $LK=1$. The finite product-sum identity `Fintype.prod_sum` factors the sum over all control words into coordinate sums. Each coordinate sum is an entry of $A_{d_l}^{-1}A_{d_l}=1$, using `Matrix.nonsing_inv_mul` with the hypothesis that its determinant is a unit, supplied by `det_A_isUnit`. Equality at every coordinate is equality of words.
3. **Enumerations.** For every such $k,d$ and every pair of bijections $b,g:\mathrm{Fin}\,N\simeq C$, `result` identifies `angleMatrix d b g` with `(K d).submatrix b g`. For a finite real square matrix, `Matrix.isUnit_det_of_left_inverse` applies to the proved identity $LK=1$, and `Matrix.isUnit_iff_isUnit_det` converts the fact that its determinant is a unit into the matrix being a unit. `Matrix.isUnit_submatrix_equiv` preserves this property under the two bijective reindexings. Neither enumeration needs Gray-code adjacency.

## Falsifier

The theorem would miss the source conjecture if the entry rule or the sequencers' outputs did not match this reading. `angleMatrix` uses the source's ordered threshold $0<b\le g$, not a symmetric sign rule. Its two enumerations are independent and bijective onto the same full Cartesian product.

The remaining source-to-formal correspondence is an argument about Appendix D, `app_3c_sequencers.tex`, lines 31–40: when every $d_l\ge2$, each prefix at level $l$ has every digit $0,\ldots,d_l-1$ as a child. Thus the single-child relabelling rule never applies, and reflecting siblings only permutes the leaves. Both trees retain the all-zero word as their first leaf, since the first parent at every layer is not reflected. The normalizer has no initial word to change. Consequently the two sequences enumerate the same Cartesian product and meet the hypotheses of `result`. This algorithmic correspondence is not formalized.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.lean`.

- **Proof.** It proves `result : claim`; `claim` universally quantifies over $k,d,b,g$ as above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible.lean.json`.

Declaration statements:

- `result`: `sha256:78a2bd30bd5f550df44c08d4cdc3e49a5862a7fbfa6c42a54b20d98a47bcfec3`;
- `claim`: `sha256:c958fad50d1379376b0976663239a0cfe0f1333c4a6903961bffbf525f24f41e`.

## Triage

Tier 1 conjecture of a 2025 preprint, preregistered in issue #23818 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $k$, every family of natural dimensions $d:\mathrm{Fin}\,k\to\mathbb N$, and every two bijective enumerations $b,g:\mathrm{Fin}(\prod_l d_l)\simeq\prod_l\mathrm{Fin}(d_l)$, the real matrix `angleMatrix d b g` is a unit, with entries given by the product of the signs that are negative exactly when $0<b(i)_l\le g(j)_l$.

**Computed, not formalized**: no numerical or finite-family computation is claimed.

**Argued, not formalized**.

- *Decisive mechanism and scope.* For all natural $m$, `E_mul_A`, `det_zeta` and `det_A_isUnit` reduce the one-coordinate sign matrix to the zeta matrix of a finite chain and establish that its determinant is a unit. For all natural $k$ and every natural dimension family $d$, `LinvPrime_mul_K` lifts those coordinate inverses to the full product. For every pair of bijective enumerations of that product, `result` transfers invertibility by reindexing. Thus the proof uses the full Cartesian indexing and permits arbitrary enumeration order; no adjacency property enters the matrix argument.
- *Degenerate cases.* If some $d_l=0$, the control set and the matrix index type are empty, so there is a unique matrix and its identity is its inverse. With no coordinates, the control set has one empty word and the empty sign product is $1$, giving the one-by-one identity matrix. Dimensions equal to one contribute only a zero digit and a sign of $1$. These unpack the definitions; the source-algorithm correspondence above is restricted to $d_l\ge2$.
- *Angle solvability.* For any parameters in `claim`, choose a two-sided inverse $U$ of $M$. For every real angle vector $\theta$, the vector $\beta=U\theta$ satisfies $M\beta=\theta$ by $MU=1$; any other solution equals $U\theta$ by $UM=1$. This is an algebraic consequence of being a unit, without a separate Lean declaration about angle vectors or circuits.
- *Neighbouring questions.* On a non-Cartesian set, digit choices are constrained jointly, so the intermediate-word sum need not factor into independent coordinate sums. The product argument supplies no classification or repair algorithm for those restricted sets. Finding the source's broader hypothesized decomposition remains open here, as do numerical conditioning and circuit optimality.
- *Effect on the paper.* Subject to the Appendix D correspondence, the result supplies the invertibility used for Cartesian control registers in Section V, including $\mathbb Z_2\times\mathbb Z_d^4$ in the resource-table caption (`sec_5_qudit-box.tex`, lines 29–32). It removes the need to assume Cartesian invertibility when solving the angle system. The proposed resource savings in that section's lines 57–66 instead assume the broader hypothesized decomposition for restricted control sets; they remain conditional. The circuit identities, resource counts and Appendix E's manual corrections are not certified by this matrix theorem.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The journal text was not reproduced. Beyond the directly checked v1 source, the arXiv version listing, INSPIRE's 21-record listing, the orchestrator's checks of the 19 citing sources and repository issues, and the search agent's searches of Zenodo, ResearchGate, SSRN, GitHub and `QSAR-UBC/QuditOpsViaLGT` are reports in #23818, not independently reproduced readings.

The Appendix D sequencer and normalizer correspondence, the explanatory consequences under “Argued, not formalized,” and the source's physical circuit implementation and resource estimates are not separate formalized results. The normalizer is specified in prose rather than as a formal algorithm. The settlement concerns the v1 Cartesian conjecture under the stated correspondence; the general restricted-control decomposition and its associated resource improvements remain open here.
