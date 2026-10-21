---
slug: la-piana-2025-c5-graph-quantum-magic-squares
bibkey: lapiana2025graphquantummagicsquares
doi: 10.48550/arXiv.2512.08797
url: https://arxiv.org/abs/2512.08797v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.result
---

# Strict containment for graph quantum magic squares on the five-cycle

## Problem

F. La Piana, *Graph Quantum Magic Squares and Free Spectrahedra*, arXiv:2512.08797v3, Question 1.3 asks:

> Given a graph Γ, does the matrix convex hull of its quantum permutation matrices P^(Γ) generate all graph quantum magic squares? That is, mconv(P^(Γ)) = M^(Γ)?

Section 4.1 names $C_5$ and the Petersen graph among the candidates for strict containment. The settlement is **Proved** for $C_5$, under the complete conventions preregistered in [#19303](https://github.com/the-omega-institute/trureturing/issues/19303):

$\operatorname{mconv}(\mathcal P^{(C_5)})_s\subseteq\mathcal M^{(C_5)}_s$ at every internal size, and some $X\in\mathcal M^{(C_5)}_2$ lies outside that hull.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Definition 2.1: positive semidefinite blocks and identity row/column sums | `IsQMS` | All external and internal natural-number sizes; complex matrices |
| Definition 3.1: adjacency-block commutation | `IsGraphQMS` | Every pair of vertices, both adjacency-filtered sums |
| Definition 3.2: graph magic squares | `M` | Set of blocks satisfying `IsGraphQMS` |
| Definition 3.2: idempotent, Hermitian graph magic squares | `P` | Both projection equations for every block |
| Definition 2.3: normalized finite blockwise compressions | `IsMatrixConvex` | All finite families, varying input sizes and all output sizes |
| Smallest containing matrix convex family | `mconv` | Intersection of every containing matrix convex family |
| Section 4.1, named candidate $C_5$ | `claim`, `result` | All-level containment and existential separation |

The source uses positive sizes and a Hermitian ambient family. The preregistered encoding uses arbitrary complex block families and includes level zero; `IsQMS` itself enforces Hermitian blocks through positivity. The size-zero matrices are unique. `Fin` indices, the matrix identity `1`, and `SimpleGraph.cycleGraph 5` implement the source's indices, identity and graph. The strictness statement is existential in the internal size, with a size-two witness; it does not assert strictness at every size.

## Motivation

The source's $C_4$ example motivates the candidate $C_5$. This settlement supplies a size-two graph quantum magic square outside the entire matrix convex hull, including compressions from arbitrary finite internal sizes.

## Gap

The literature screen recorded in #19303 reads arXiv v1–v3, the predecessor papers arXiv:1912.07332, 2209.10230 and 2304.10920, and MathDB. The search seat reports zero citations in Semantic Scholar and OpenAlex. The orchestrator checked Question 1.3, Definitions 2.1, 2.3, 3.1–3.2, Section 4.1 and Appendix A.2. No settlement for this candidate was found in that searched scope. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The private theorem `P_dihedral` constructs positive families $R,S$ for each graph quantum permutation matrix on $C_5$, with blocks $X_{ij}=R_{i-j}+S_{i+j}$. Products of entries in the first two rows construct these families; orthogonality and the cycle recurrence extend the identity to every row. `matrix_convex_dihedral` preserves this form under normalized blockwise compressions. Thus `hull_dihedral` gives the same form for every member of the matrix convex hull.

The separating blocks are

$B_{ij}=\frac1{25}\begin{pmatrix}5+a_{i-j}&b_{i+j}\\b_{i+j}&5-a_{i-j}\end{pmatrix}$,

where $a=(3,-3,0,0,0)$ and $b=(4,-4,0,0,0)$, with indices modulo five. `witness_mem_M` verifies positivity and the row, column and graph relations. Four rank-one blocks have distinct kernels. The imported theorem `D5.S3.Quantum.Measurement.AntidistinguishabilityGram.psd_summand_kills_kernel` is applied in `positive_summand_kernel`; `witness_not_dihedral` uses it to force $R_0=R_1=0$. This contradicts unequal top-left entries of two blocks sharing the same $S$ summand. `result` combines this separation with `hull_subset_M`.

## Falsifier

A failure would be a graph quantum permutation input outside the proved dihedral form, a blockwise normalized compression violating that form, or positive dihedral summands for the explicit separating square. Each contradicts a statement used by `result`. A source-level conclusion for other graphs or a uniform odd-cycle Lean theorem is outside this settlement.

## Evidence

The canonical source is `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.lean`, under its matching namespace. Its only public theorem is `result`; the auxiliary theorem declarations are private. The published kernel lemma retains its existing proof and has a complete node in its owner's Scribe. The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}.

The escape audit is unfinished for `D5.S3.Quantum.LaPianaGraphQuantumMagicSquares.result` and the published kernel lemma: [#19372](https://github.com/the-omega-institute/trureturing/issues/19372). The missing evidence is a faithful complete dependent-family realization, source reconstruction, lawful enrolled readout, variation, sensitivity and observational dependence. No validated registration is claimed.

### Exact experiment

[Experiment directory at commit `d75a7de610b2011303bab2732d23f5c64ebb811c`](https://github.com/the-omega-institute/trureturing-experiments/tree/d75a7de610b2011303bab2732d23f5c64ebb811c/docs/reports/la-piana-2025-c5-graph-quantum-magic-squares).

Command: `python3 /Users/auric/trureturing-experiments/docs/reports/la-piana-2025-c5-graph-quantum-magic-squares/check.py`; exit 0. Script SHA-256: `fdbcd3de2eb8325a1ed7252260872e6a6c897d3a3a93ee62da9c85746056f81a`. Its bytes equal that pinned file. For exactly $n\in\{5,7,9,11,13\}$, exact arithmetic verifies positive semidefinite blocks, identity row and column sums, the graph relation, the four rank-one blocks and their separation data. Every listed check passes. This computation does not establish a uniform odd-cycle theorem or classify all quantum permutation matrices for those sizes.

## Triage

Tier 1; resolution `Proved` for the named $C_5$ candidate. Admission basis: `open-problem-resolution (#19303; Proved)`. There is no digestion atom; the settling GID is `D5/S3/Quantum/LaPianaGraphQuantumMagicSquares.result`.

### What the settlement shows

| Item | Evidence kind and result |
| --- | --- |
| $C_5$ strict containment with an internal-size-two witness | **Kernel-checked:** `result` proves strict containment; its proof uses the size-two witness verified by `witness_mem_M` and separated by `witness_not_dihedral`. |
| Decisive mechanism at $C_5$, including arbitrary finite dilation sizes | **Kernel-checked:** `P_dihedral`, `matrix_convex_dihedral` and `hull_dihedral` force a positive circulant-plus-anti-circulant form; `witness_not_dihedral` excludes it using the rank-one kernels. |
| Odd-cycle construction at $n=5,7,9,11,13$ | **Computed:** the exact experiment verifies the witness relations and separation data only at these five sizes. |
| Uniform family for every odd $n\ge5$ | **Open:** #19303 contains the search seat's proposed extension; a uniform theorem is not formalized here. The computation alone does not prove its quantum-symmetry classification or hull description. |
| Even $n\ge6$ | **Open:** the map $(i,j)\mapsto(i-j,i+j)$ is no longer bijective, so the stated separation argument does not directly transfer. |
| Petersen graph | **Open:** no settlement is asserted. |
| General vertex-transitive graphs | **Open:** no classification or uniform strictness theorem is asserted. |

For $C_5$, Question 1.3 has a negative answer. The source's independent $C_4$ construction, commutant-dimension computations and free-spectrahedral results keep their stated scope; this module does not alter them. No quantitative separation distance or minimal internal-size theorem is asserted.

## ASSUMED-UNVERIFIED

Completeness of the literature exclusion and worldwide priority are `ASSUMED-UNVERIFIED`. The arbitrary-complex-family and size-zero conventions are the explicit preregistration boundary. The uniform odd-cycle extension, even cycles, Petersen graph and general vertex-transitive graphs remain outside the kernel-checked settlement. The escape audit remains unfinished as linked above.
