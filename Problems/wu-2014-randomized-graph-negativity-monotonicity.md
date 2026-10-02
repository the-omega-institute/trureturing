---
slug: wu-2014-randomized-graph-negativity-monotonicity
bibkey: wu2014randomized
doi: 10.1103/PhysRevA.89.052335
url: https://arxiv.org/abs/1403.3828v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result
---

# Monotonicity of the negativity of randomized graph states

## Problem

J.-Y. Wu, M. Rossi, H. Kampermann, S. Severini, L. C. Kwek, C. Macchiavello,
D. Bruß, *Randomized Graph States and their Entanglement Properties*, Phys.
Rev. A 89, 052335 (2014), arXiv:1403.3828v3, Section V:

> However, even though this conjecture is supported by numerical evidence,
> it is an open question whether the monotonic behavior of the negativity in
> terms of the randomness $p$ is a common feature to all RG states.

The randomized graph state of a graph $G$ is
$\rho^p_G=\sum_{F\subseteq E(G)}p^{|F|}(1-p)^{|E(G)\setminus F|}
|F\rangle\langle F|$, where $|F\rangle=\prod_{ab\in F}\mathrm{CZ}_{ab}
|+\rangle^{\otimes n}$, and the negativity across a bipartition $A|B$ is
$N(\rho)=(\|\rho^{\Gamma_A}\|_1-1)/2$, evaluated "with respect to all
possible bipartitions of the qubits". The conjecture is that $N$ increases
monotonically in $p$; the paper reports it numerically for the complete
graphs $K_n$ and the star graphs $S_n$ with $n\le4$.

## Motivation

A randomized graph state models the preparation of a graph state with
probabilistic entangling gates: every controlled-Z gate succeeds with
probability $p$ and the record of which gates succeeded is lost. At $p=0$
the state is the product state $|+\rangle^{\otimes n}$ and at $p=1$ it is
the graph state of $G$, so one expects more entanglement for more reliable
gates. The question asks whether this holds for every graph and every cut.
The frozen declaration
`D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result`
answers it negatively.

## Gap

Issue #12382 classifies the question as Tier 1 and records the checks made
before any Lean:

- arXiv:1403.3828 v3 (2014-06-03) is the latest version and the published
  version, and the question is printed as quoted;
- Salem–Silva–Andrade, arXiv:2310.20418v2 (Phys. Rev. A 109, 012416,
  2024), Sec. IV, report non-monotonic entanglement only for randomized
  hypergraph states with hyperedges of different orders and write that
  "such behavior could not be observed in RG states"; their
  arXiv:2506.20075v2 (2026), Fig. 3 caption, states "Monotonicity holds
  for hypergraphs with uniform hyperedge orders"; the review
  Poderini–Bruß–Macchiavello, arXiv:2603.10917v1 (2026), Sec. III.4,
  attributes non-monotonicity to non-uniform hypergraphs;
- noisy and percolated graph-state results (Aolita et al.,
  arXiv:1006.3152; Kieling–Rudolph–Eisert, quant-ph/0611140) concern other
  models.

These are orchestrator-reported and seat-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty. Convexity of the trace norm bounds the negativity of the mixture
from above by the average negativity of the graph states $|F\rangle$, so
the large negativity of some subgraph states does not by itself give a
lower bound for the mixture.

## Route

$G=K_{3,3}$ on $\{0,\dots,5\}$ with parts $A=\{0,2,4\}$ and
$B=\{1,3,5\}$, $p=97/100$ and $q=1$.

1. Expanding the product over the edges,
   $\rho^p_G(x,y)=2^{-n}\prod_{ab\in E}(p\,c_{ab}+1-p)$ with $c_{ab}=1$ if
   $x_ax_b=y_ay_b$ and $c_{ab}=-1$ otherwise; so the partial transpose
   $X_p=(\rho^p_G)^{\Gamma_A}$ has entries $(1-2p)^{d}/64$, where $d$
   counts the edges on which the exchanged labels disagree.
2. At $p=1$, with $u_{ij}(x)=[\,|x_A|\equiv i\ (2)\,](-1)^{j|x_B|}$,
   $w=u_{01}-u_{10}$ and $v=u_{01}+u_{10}$, the entrywise identity
   $X_1+\tfrac1{128}ww^{\mathsf T}=\tfrac1{64}(u_{00}u_{00}^{\mathsf T}
   +u_{11}u_{11}^{\mathsf T})+\tfrac1{128}vv^{\mathsf T}$ writes $X_1$ as a
   difference of two positive semidefinite matrices with traces $3/2$ and
   $1/2$; the triangle inequality gives $\|X_1\|_1\le2$, so
   $N(\rho^1_G)\le1/2$.
3. At $p=97/100$, fourteen pairwise orthogonal integer vectors
   $u_j\in\mathbb Z^{64}$ give the projection
   $P=\sum_ju_ju_j^{\mathsf T}/\|u_j\|^2$ and the unitary $U=I-2P$; by the
   variational formula $\|X\|_1\ge\operatorname{Re}\operatorname{tr}(UX)$,
   $\|X_{97/100}\|_1\ge1-2\sum_ju_j^{\mathsf T}X_{97/100}u_j/\|u_j\|^2
   =2.0280536\ldots>2$.
4. Hence $N(\rho^{97/100}_G)>1/2\ge N(\rho^1_G)$ with $97/100\le1$.

## Falsifier

The kernel-checked `result` is the negation of the universal statement
over finite simple graphs on `Fin n`, subsets $A$ of the vertices and all
real $0\le p\le q\le1$. The basis states are the maps `Fin n → Fin 2`, the
graph state of an edge set is its product of controlled-Z phases times the
amplitude $2^{-n/2}$ of $|+\rangle^{\otimes n}$, the mixture runs over the
subsets of `G.edgeFinset`, the partial transposition exchanges the $A$
parts of the row and column labels, and the trace norm is the frozen
`FiniteTraceDistance.traceNorm`, $\operatorname{Re}\operatorname{Tr}
\sqrt{X^\dagger X}$. A measure that is an increasing function of $N$, such
as the logarithmic negativity $\log_2(2N+1)$, is refuted as well;
restricting the question to $K_n$ and $S_n$ changes the question.

## Evidence

Exhaustive NumPy scan of the connected graphs on 4–6 vertices, all
bipartitions and $p\in\{0,0.01,\dots,1\}$ (issue #12382): five pairs
$(G,A)$, all on 6 vertices, show a decrease; none on 4 or 5 vertices. The
largest is this example: $N(\rho^p_{K_{3,3}})$ rises above $1/2$ on
$[0.936,0.999]$ with maximum $0.5140464\ldots$ near $p=0.97$, and the
derivative at $p=1$ is about $-1$ (finite difference). The exact lower
bound of step 3 is $N\ge0.5140268\ldots$. The certificate vectors split by
the $S_3\times S_3$ symmetry of the parts (six in the symmetric sector,
two in each mixed sector, four in the standard–standard sector).

The canonical source is
`D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.lean`. Its
public declarations are `Qubits`, `czPhase`, `plusState`, `graphState`,
`rgState`, `partialTranspose`, `negativity`, `claim`, `k33`,
`partA` and `result`; the trace norm and its lemmas are frozen in
`D5/S3/Quantum/Foundation/FiniteTraceDistance`; `k33` carries a decidable
adjacency instance. The frozen module state has statement identity
`sha256:e6b7c60cb6c1860ae73bb8c939e895f78caaea0453eb3bca8ad5d4e2c47fed0a`. The
result declaration has statement identity
`sha256:8699682eb0805d4dcf1355be31c5dac754e3a40e309a3d295ac441cf8ab56906`. The
Freeze event is
`sha256:7b4331af2c3bbbd8cf354609e89d5137abeb2a7daaf7722b9d52a233f58ca751`; its
project-level frozen prerequisite is the Freeze event of
`D5/S3/Quantum/Foundation/FiniteTraceDistance`. The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 published question; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue
#12382). Utility kind `certified-instance`, basis `refutes` the module's
`claim`.

### What the settlement shows

- **Proved by `result`:** the negativity of randomized graph states is not
  monotone in $p$: for $K_{3,3}$ across its two parts it is larger at
  $p=97/100$ than at $p=1$.
- **Proved inside the proof of `result`:** the closed form
  $(1-2p)^d/64$ of the partial transpose for $K_{3,3}$ at every $p$; the
  decomposition of step 2, giving $N(\rho^1_{K_{3,3}})\le1/2$; and the
  bound $\|X_{97/100}\|_1>2$ from the explicit unitary $I-2P$.
- **Mechanism (computed, not stated in Lean):** a graph state across a cut
  has negativity $(2^r-1)/2$, where $r$ is the rank over GF(2) of the
  biadjacency matrix of the cut (checked by singular values for all $512$
  spanning subgraphs of $K_{3,3}$). The biadjacency matrix of $K_{3,3}$ is the all-ones $3\times3$
  matrix, $r=1$, so the endpoint has $N=1/2$; deleting any one edge raises
  $r$ to $2$ ($N=3/2$), and among the $512$ spanning subgraphs $462$ have
  $r\ge2$. Near $p=1$ the mixture puts weight about $9(1-p)$ on the
  one-edge deletions, and the computed negativity grows. In the scan, all
  five decreasing pairs have $r=1$ for the full graph and a single-edge
  deletion with $r=2$; among the $3273$ pairs where no single-edge deletion
  raises $r$, none decreases, and $551$ of the $556$ pairs where one does
  are still monotone on the grid.
- **Computed, not in Lean:** $N(\rho^p_{K_{3,3}})$ also decreases slightly
  on $[0.405,0.488]$ (from $0.10323$ to $0.10213$); $K_{4,2}$ with $A$ the
  part of size $2$ decreases by $1.8\times10^{-4}$ between $p=0.41$ and
  $0.47$ while its maximum $1/2$ is at $p=1$.
- **Follows from it (not stated in Lean):** the statements of
  Salem–Silva–Andrade that non-monotonic behaviour "could not be observed in
  RG states" (2024) and that monotonicity holds for hypergraphs with
  uniform hyperedge orders (2026) do not extend to all ordinary graphs,
  since $K_{3,3}$ is 2-uniform; by continuity the decrease also holds
  against some $q<1$.
- **Open here:** a characterization of the pairs $(G,A)$ with monotone
  negativity (the rank condition above is necessary on the scanned graphs
  but not sufficient, and its necessity in general is not proved); whether
  the complete graphs $K_n$ and the stars $S_n$, the families of the
  paper's numerics, are monotone for all $n$; and the sign of $dN/dp$ at
  $p=1$, which the first-order perturbation of the trace norm ties to the
  kernel of $(|G\rangle\langle G|)^{\Gamma_A}$.

## ASSUMED-UNVERIFIED

Mansour et al., Laser Phys. 31, 035201 (2021), "Decay of negativity of
randomized multiqubit mixed states", was not read in full; Salem–Silva–
Andrade (2024, ref. [40]) describe it as observing monotonic negativity for
states generated by random Ising-type entangling operators. The literature
checks do not establish worldwide priority. The Lean kernel verifies the
encoded statement and its axiom closure; its correspondence to the paper,
including the reading of the question as a universal statement over all
graphs, bipartitions and pairs $p\le q$, is checked by reading the source
and the definitions.
