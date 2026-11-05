---
slug: coutinho-baptista-2023-normalized-laplacian-tree-state-transfer-refutation
bibkey: coutinhobaptista2023normalized
doi: 10.1080/03081087.2023.2236282
url: https://arxiv.org/abs/2209.04668v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/NormalizedLaplacianTreeStateTransfer.result
---

# A seventeen-vertex tree admits normalized-Laplacian perfect state transfer

## Problem

G. Coutinho and P. F. Baptista, *Quantum Walks in the Normalized Laplacian*, arXiv:2209.04668v1 (2022; journal publication online 2023, DOI 10.1080/03081087.2023.2236282), Conclusion, `norm-laplacian-v2.tex`, line 427:

> For trees, we were not able to show a complete analogous result to the combinatorial Laplacian case --- that is, that perfect state transfer does not occur. We were however able to significantly restrict the possible cases, and therefore we conjecture that apart from the paths on $2$ and $3$ vertices, no tree admits perfect state transfer according to the normalized Laplacian.

This quotation was checked against the v1 TeX source, md5 `b274bca76e7a9e881ea5b092556075a9`. The definitions preceding equation (1), lines 89–98, and the transfer definition, lines 161–164, use $\mathcal L=D^{-1/2}(D-A)D^{-1/2}$, $U(t)=\exp(it\mathcal L)$ and $U(\tau)e_a=\lambda e_b$ for a complex unit $\lambda$. See also [the literature note](../Library/QuantumContext/coutinhobaptista2023normalized.md).

Issue [#20154](https://github.com/the-omega-institute/trureturing/issues/20154) fixes the statement: for every natural number $n\ge4$, every simple graph $G$ on $\operatorname{Fin}(n)$ with decidable adjacency, and every pair of distinct vertices $a,b$, if $G$ is a tree then there are no $\tau\in\mathbb R$ and $c\in\mathbb C$ with $|c|=1$ and $U(\tau)e_a=c e_b$. This is `claim`, and it is refuted. The two- and three-vertex trees are precisely the excluded paths.

## Motivation

The source studies trees as quantum-network architectures requiring few edges. Excluding transfer on all larger trees would extend the combinatorial-Laplacian obstruction to the normalized-Laplacian walk. A tree supporting transfer distinguishes these Hamiltonian models and shows that acyclicity alone does not prevent exact transfer in the normalized model.

## Gap

The bounded literature check recorded in #20154 reports:

- The orchestrator found only arXiv v1; the journal text was not read.
- Semantic Scholar listed two citing works. The orchestrator read their TeX and reported that Kong, Wyman and Xi (2024, arXiv:2401.06022) mention state transfer only in their introduction, while Wyman and Xi (2023, arXiv:2304.04659) do not discuss it. OpenAlex counted no citations of the journal version.
- The orchestrator's arXiv abstract search for both “normalized Laplacian” and “state transfer” returned the source and Alvir et al. (2016, arXiv:1409.5840). No settlement was found in that search or in the repository's Problems, Library and issue search.
- The search seat reported that a characteristic-polynomial formula of Das–Sun (2016, *Taiwanese Journal of Mathematics* 20, 491–507), combined with the source's characterization, yields this transfer. That prior-implication reading was not independently reproduced here; no claim of a new spectral formula or exhaustive priority is made.

`not-found-in-searched-scope` refers to an explicit settlement of the conjecture within that recorded search scope.

## Route

Let $c$ be adjacent to two leaves $u,v$ and to $x_1,\ldots,x_7$, and let each $x_i$ be adjacent to one further leaf $y_i$. These are all the edges. The graph has $17$ vertices and $16$ edges, every vertex is reachable from $c$, and its degrees are $9$ at $c$, $2$ at each $x_i$, and $1$ at the leaves. In the Lean graph, $u=0$, $v=1$, $c=2$, $x_i=2i+1$ and $y_i=2i+2$ for $1\le i\le7$.

1. **The antisymmetric mode.** $e_u-e_v$ has normalized-Laplacian eigenvalue $1$.
2. **The symmetric modes.** Write a vector constant on the seven arms by its entries $(u,v;c;x_i;y_i)$. Four eigenvectors are $w_0=(1,1;3;\sqrt2;1)$, $w_2=(1,1;-3;\sqrt2;-1)$, $w_{2/3}=(1,1;1;-\sqrt2/7;-3/7)$ and $w_{4/3}=(1,1;-1;-\sqrt2/7;3/7)$, with eigenvalues given by their subscripts. The exact decomposition is $e_u+e_v=w_0/16+w_2/16+7w_{2/3}/16+7w_{4/3}/16$.
3. **The phases.** At $t=3\pi$, the four symmetric phases are $1$, whereas the antisymmetric phase is $-1$. Thus $U(3\pi)$ fixes $e_u+e_v$ and negates $e_u-e_v$.
4. **Transfer.** Since $e_u$ is half the sum of these two vectors, $U(3\pi)e_u=e_v$. The private declarations `tree_isTree` and `transfer` supply the tree and transfer certificates used by `result : ¬ claim`.

## Falsifier

The counterexample must use the source's Hamiltonian and exact coordinate-state transfer. The module defines:

- `normalizedLaplacian` by multiplying the combinatorial graph Laplacian on both sides by the diagonal inverse square roots of the degrees, as a complex matrix;
- `walk` with the source's positive sign, $\exp(it\mathcal L)$;
- `PST` by existence of a real time and a scalar of norm one giving equality of the entire evolved coordinate vector with the target coordinate vector;
- `claim` with the universal quantifiers, tree hypothesis, lower bound $n\ge4$ and distinctness condition stated above.

The normalized-Laplacian definition extends to isolated vertices using inverse zero; a tree on at least four vertices has none. `PST` does not require a positive time, but the exhibited time $3\pi$ is positive. The witness has phase $1$ and exact vector equality, so it also meets the source's transfer definition without a numerical tolerance or an ambiguity about global phase.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/NormalizedLaplacianTreeStateTransfer.lean` (267 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It applies `EnergyEigenstateStationarity.exp_mulVec_of_eigenvector` to the certified modes and combines their evolutions by matrix-vector linearity.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/NormalizedLaplacianTreeStateTransfer.lean.json`, statement `sha256:3b5928f1a3c40af655086887455794fc884a1ccf7b230212cb5ba99d64e07b3e`.

Declaration statements:

- `result`: `sha256:87e58f30451611d0a6ae70ebbad14e191797af13f8cc38c93c86aef658c9a6bd`;
- `claim`: `sha256:4e576d6b7aea4437b44da5583e95bfe42c50615af040b9daaa8f0292b7c0e906`.

## Triage

Tier 1 conjecture of a 2022 preprint (journal publication online 2023), preregistered in issue #20154 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed, and the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal assertion that every finite simple tree on at least four vertices forbids perfect state transfer between distinct vertices is false, with precisely the graph, real-time and unit-phase conventions of `claim` above. This is `¬ claim`.

**Computed, not formalized** (independent Python/SymPy and NumPy/SciPy calculations):

- Exact arithmetic gives the full $17$-vertex spectrum $0,\ 1-\sqrt2/2\ (\times6),\ 2/3,\ 1,\ 4/3,\ 1+\sqrt2/2\ (\times6),\ 2$. The four symmetric eigenvectors, endpoint decomposition and exact spectral evolution give $U(3\pi)_{vu}=1$ and $U(3\pi)_{uu}=0$. The full-spectrum assertion is not a theorem of the module.
- For the analogous tree with $m$ length-two arms and the same two leaves, numerical diagonalization at $(m,t)=(7,3\pi)$ and $(23,5\pi)$ gives maximum coordinate errors from $e_v$ of $1.18\times10^{-14}$ and $3.47\times10^{-15}$, respectively. These are floating-point checks.
- For the tested values $m=5,6,8$, perfect transfer was not observed on the grid $t=0,0.01,\ldots,60$. The largest sampled transfer amplitudes were respectively $0.9910722$, $0.9955636$ and $0.9967984$. This grid excludes no untested time or tree.
- A symbolic determinant for the arm-symmetric normalized-adjacency block, with $d=m+2$, is $(z^2-1)(z^2-1/d)$.

**Argued, not formalized.**

- *Failure mechanism.* The irrational eigenvalues in the full spectrum do not obstruct these endpoints. Arm-difference vectors have zero entries at $u,v,c$; if their arm coordinates satisfy $\sum_i x_i=\sum_i y_i=0$, the normalized adjacency acts by $(x_i,y_i)\mapsto(y_i/\sqrt2,x_i/\sqrt2)$. This invariant subspace has normalized-Laplacian eigenvalues $1\pm1/\sqrt2$ and is orthogonal to both endpoint states. Only the rational symmetric modes and the antisymmetric eigenvalue $1$ enter the transfer. Acyclicity does not exclude their exact phase alignment.
- *A family and its phase obstruction.* For an integer $m\ge1$, the analogous tree has $2m+3$ vertices and central degree $d=m+2$. On the orthonormal basis $((e_u+e_v)/\sqrt2,e_c,m^{-1/2}\sum_i e_{x_i},m^{-1/2}\sum_i e_{y_i})$, normalized adjacency has zero diagonal and consecutive off-diagonal entries $\sqrt{2/d},\sqrt{m/(2d)},1/\sqrt2$. Expanding its tridiagonal determinant gives $(z^2-1)(z^2-1/d)$, so the symmetric normalized-Laplacian eigenvalues are $0,2,1\pm1/\sqrt d$. All off-diagonal entries are nonzero: an eigenvector with zero first coordinate would have all coordinates zero by successive row equations. Consequently all four eigenvalues occur in the symmetric endpoint support. Together with $e_u-e_v$, this accounts for the endpoint states. Transfer requires the common symmetric phase to be $1$ because eigenvalue $0$ occurs, and the antisymmetric phase to be $-1$. Hence $t=r\pi$ for an odd integer $r$, and $r\pm r/\sqrt d$ must both be even integers. Equivalently $r/\sqrt d$ is an odd integer. Therefore $\sqrt d$ is rational, hence an integer because $d$ is an integer, and it is odd. Conversely, if $d=q^2$ for an odd integer $q\ge3$, then $t=q\pi$ gives all four symmetric phases $1$ and the antisymmetric phase $-1$. Thus, for this family and this leaf pair, transfer occurs exactly when $m+2$ is an odd square; $m=q^2-2$ gives $2q^2-1$ vertices. This family argument is not part of `result`. It identifies $17$ as the smallest member of this family admitting that transfer, without deciding the smallest counterexample among all trees.
- *Surviving restrictions and open cases.* The source's tree corollary, TeX lines 391–394, states: “Let $G$ be a tree on three or more vertices, admitting perfect state transfer between vertices $a$ and $b$. If $a$ and $b$ are in the same bipartite class, then they are leafs attached to the same vertex.” The witness has exactly those two leaves and satisfies this necessary restriction. A non-transfer condition excluding an odd-square central degree works for this leaf pair within the family by the preceding argument; extending such a condition to arbitrary trees is open. A classification of all transferring trees, existence of a smaller counterexample outside this family, and transfer between opposite bipartite classes in trees larger than $P_2$ are not settled here.
- *Effect on the paper.* The conjecture is in the final Conclusion paragraph; no preceding theorem uses it as a premise. The counterexample overturns that conjecture and meets the paper's same-class restriction. The source also states at TeX line 425, citing Alvir et al. (2016, arXiv:1409.5840): “perfect state transfer occurs if and only if the path has $2$ or $3$ vertices.” This path statement is unaffected: the witness has a degree-$9$ vertex and is not a path. The source's preceding spectral characterization and necessary tree restrictions are not replaced by a classification of all trees through this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check in #20154 does not establish exhaustive worldwide novelty or priority. The journal version, the full texts of the two citing works, the original arXiv search, the Semantic Scholar and OpenAlex counts, and the repository-wide search reported there were not independently reproduced here. The citing works' author metadata were checked on arXiv; their reported contents remain attributed to the preregistration's orchestrator. The Das–Sun prior-formula reading and its implication reported by the search seat were not reproduced. The independent checks above reproduce the registered witness and selected family computations, not the original computation scripts or grid specification in #20154.

The source's SAGE/CoCalc search concerning trees through $16$ vertices (TeX line 415) was not reproduced. The path theorem quoted from the source was not independently checked in Alvir et al.; it and the source's other general spectral and tree results are literature statements, not conclusions formalized by this module. All full-spectrum, numerical, symbolic-family and explanatory assertions labelled “Computed, not formalized” or “Argued, not formalized” remain outside the Lean settlement. The family-wide characterization, global minimality and the remaining tree-classification questions are not formal claims of `result`.
