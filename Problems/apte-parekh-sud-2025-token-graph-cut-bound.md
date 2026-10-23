---
slug: apte-parekh-sud-2025-token-graph-cut-bound
bibkey: apteparekhsud2025tokenbounds
doi: null
url: https://arxiv.org/abs/2506.03441v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.result
---

## Problem

Apte, Parekh and Sud, *Conjectured Bounds for 2-Local Hamiltonians via Token Graphs*, arXiv:2506.03441v2, Appendix D.2, Conjecture 7, page 39, states:

> In contrast, the following bound was shown to hold on our dataset
>
> For all $G$ and for all $1\le k\le\lfloor n/2\rfloor$, $\lambda_{\min}(A(F_k(G)))\ge-(C(G)+M_k(G))/2$.

Here $F_k(G)$ is the token graph, $C(G)$ is the maximum cut weight, and $M_k(G)$ is the maximum matching weight among matchings with at most $k$ edges. The settlement is **Refuted** by a unit-weight simple graph with $n=200$ and $k=100$.

### Statement echo

| source clause | Lean counterpart | fidelity |
| --- | --- | --- |
| Finite graph $G$ on $n$ vertices | `claim` quantifies `SimpleGraph (Fin n)`. | A labelled finite simple graph with unit edge weights is within the source's universal range. |
| Token graph $F_k(G)$ | Frozen `TokenGraphLaplacianRadiusRefutation.tokenGraph` | Vertices are $k$-subsets; adjacency moves one token along an original edge. |
| Maximum cut $C(G)$ | `crosses` and `maxCut` | Exactly one endpoint is in the cut; each unordered unit-weight edge is counted once; the supremum ranges over all cuts. |
| Matching weight with at most $k$ edges | `maxMatchingLe` | Edge subsets have pairwise disjoint endpoint sets and cardinality at most $k$; weight equals cardinality. |
| Minimum adjacency eigenvalue | `lambdaMin` applied to the real adjacency matrix | Minimum of the finite real Hermitian eigenvalue family; the zero extensions for empty or non-Hermitian matrices are unused. |
| $1\le k\le\lfloor n/2\rfloor$ | The two hypotheses of `claim` | Natural division by two gives the floor. |
| The proposed lower bound | The conclusion of `claim` | Cut and matching cardinalities are cast to real numbers before division by two. |
| Failure of the universal assertion | `result : ¬ claim` | The instance uses the five-cycle blow-up with block size 40. |

Decidable adjacency is an implementation instance, not a restriction of the finite graphs. Connectedness and bipartiteness are not extra hypotheses. Public definitions display the literal source notions; the phase vector, block occupancies and other proof constructions are private.

## Motivation

The source uses the proposed cut bound to obtain an XY-Hamiltonian upper bound and conditional approximation guarantees. The settling GID is `D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.result`; the source locator and quoted definitions are in `Library/GraphInvariants/apteparekhsud2025tokenbounds.md`.

## Gap

Conjecture 7 remains stated in version 2. The preregistration [#15417](https://github.com/the-omega-institute/trureturing/issues/15417) records the source and bounded literature screen: Bakshi–Basu–Kothari–Li (arXiv:2605.14994), Jiang (arXiv:2609.25037), arXiv:2512.09896, and the token-graph papers arXiv:2610.00418 and 2610.00500 did not supply a settlement of this cut bound. Absence of a settlement outside that searched scope is unverified.

## Route

Let $G_s$ replace each vertex of $C_5$ by an independent block of size $s$, and each cycle edge by a complete bipartite graph. For even $s$, put $N=5s$ and $k=N/2$. Write $b(v)$ for the block index, set $z=(-4+3i)/5$, and use $w(S)=\prod_{v\in S}z^{b(v)}$. Symbolic token-move counting reduces its energy to an edge sum, and a real/complex Rayleigh bridge bounds the least eigenvalue. Affine rounding of the five cut occupancies bounds the maximum cut. Lean checks the instance $s=40$; the uniform family derivation below is proved in prose.

## Falsifier

At $s=40$, the private helpers `phi40_quotient`, `maxCut40`, `maxMatchingLe_le` and `lambdaMin40` on `result`'s proof path establish

$$R_{40}=-\frac{646912}{199}<-3250,\qquad C(G_{40})\le6400,\qquad M_{100}(G_{40})\le100.$$

Thus the conjectured lower bound is at least $-3250$ while the least adjacency eigenvalue is at most $-646912/199$. The strict gap is $162/199$.

## Evidence

The kernel-checked public declaration is `D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation.result`. Its proof uses the module's private token-counting, phase-energy, cut-rounding and Rayleigh lemmas. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The generic counting helper is bind-only and supplies no escape witness; the module uses `open-problem-resolution (#15417; Refuted)` admission.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment entry: [token-graph cut-bound checks](https://github.com/the-omega-institute/trureturing-experiments/tree/45adfe6badbabfd828163da46be8c2e1550b3e50/docs/reports/apte-parekh-sud-2025-token-graph-cut-bound-refutation), `python3 check.py`, exit 0, script SHA-256 `4f539059cc96f1f890083713d626b2d79b895c784ea6354209d34c923d93687b`, final result `bad= 0`. The tested scope is:

- Brute-force token-graph Rayleigh quotients at $s=2$ (252 vertices, $-8.984888889$) and $s=4$ (184756 vertices, measured $-34.047999996$, formula $-34.048000000$), with relative tolerance $10^{-7}$.
- Exact rational phase identity $4\operatorname{Re}z+\operatorname{Re}z^4=-2527/625$.
- All $2^{10}$ cuts at $s=2$, giving $C(G_2)=16$, and all 32 five-cycle block patterns, with maximum four crossing block edges.
- Explicit perfect matchings at $s=2,4,6,40$, each of size $5s/2$.
- Exact rational threshold checks for every even $2\le s\le200$, and the exact value $R_{40}=-646912/199$.
- Dense numerical diagonalization at $s=2,k=5$, yielding $\lambda_{\min}\approx-9.561775\ge-10.5$.

These finite computations do not establish the uniform family or settle every $s<40$ case.

## Triage

| item | status | evidence kind and scope |
| --- | --- | --- |
| The phase vector violates the token-graph cut bound at $s=40$, $n=200$, $k=100$. | proved | Kernel-checked `result`, using private `counting_identity`, `phi40_energy`, `phi40_quotient`, `lambdaMin40`, `maxCut40` and `maxMatchingLe_le`. |
| Every even $s\ge40$ gives a counterexample. | proved | Proved in prose in the family derivation below; no general-$s$ Lean theorem is delivered. |
| The unconditional XY upper bound in Corollary 12 fails on that family. | proved | Proved in prose below using the source's Fact 2; no XY Lean theorem is delivered. |
| Phase, quotient, cut, matching, threshold and small-case spectral readings. | computed | The pinned experiment entry above, command `python3 check.py`, exit 0 and the stated SHA-256; exactly the finite scopes listed there. |
| Whether the cut bound holds for the remaining $s<40$ cases, or other graph families. | open | The computation checks the full spectral bound only at $s=2$; failure of the phase-vector violation test at smaller $s$ does not prove the conjecture there. |
| Approximation ratios and repaired cut-based bounds. | open | The conditional implications retain their logical form; this counterexample does not itself refute the approximation ratios. |

### What the settlement shows

**Family, proved in prose.** Since $|z|=1$, every component of $w$ has modulus one and $w^*w=\binom Nk$. For an oriented original edge $(u,v)$, a token move can start precisely in the $k$-subsets containing $u$ and omitting $v$. Removing $u$ bijects these subsets with the $(k-1)$-subsets of the other $N-2$ vertices, giving multiplicity $\binom{N-2}{k-1}$. For that move the phase ratio is $z^{b(v)-b(u)}$. Four cycle edges join successive indices and the wraparound edge joins 4 and 0, so summing both orientations and the $s^2$ vertex pairs per block edge gives

$$w^*Aw=2s^2\bigl(4\operatorname{Re}z+\operatorname{Re}z^4\bigr)\binom{N-2}{k-1}.$$

The phase coefficient equals $-2527/625$, and

$$\frac{\binom{N-2}{k-1}}{\binom Nk}=\frac{k(N-k)}{N(N-1)}=\frac{5s}{4(5s-1)}.$$

The Rayleigh principle for a real symmetric matrix also applies to complex vectors: its real and imaginary parts give real quadratic forms whose sum is $w^*Aw$, while their squared norms sum to $w^*w$. Therefore

$$\lambda_{\min}(A(F_k(G_s)))\le R_s=-\frac{2527s^3}{250(5s-1)}.$$

For a cut with block occupancies $x_i\in[0,s]$, its weight is $\sum_{i=0}^4[x_i(s-x_{i+1})+(s-x_i)x_{i+1}]$, with indices modulo 5. It is affine in each occupancy. Replacing each occupancy by an endpoint that does not decrease the weight bounds every cut by an all-or-nothing block cut. A cut of an odd five-cycle crosses at most four edges, and the block pattern $(0,s,0,s,0)$ attains four. Hence $C(G_s)=4s^2$ in prose. Unit weights give $M_k(G_s)\le k$. To attain $k=5s/2$, divide each block into two halves, assign one half to its preceding cycle edge and the other to its succeeding edge, and pair the assigned halves along each edge. These five disjoint half-block matchings cover every vertex once. Thus $M_k(G_s)=M(G_s)=5s/2$ in prose; Lean needs only the upper bounds at $s=40$.

The amount by which the proposed lower bound exceeds $R_s$ is

$$-\frac{4s^2+5s/2}{2}-R_s=\frac{s(108s^2-4250s+1250)}{1000(5s-1)}.$$

For $t=s-40\ge0$, the numerator polynomial is $108t^2+4390t+4050>0$. The denominator is positive, so every even $s\ge40$ violates the bound. The mechanism is a phase energy with a quadratic advantage over maximum cut, while the matching correction grows only linearly.

**XY consequence, proved in prose.** Fact 2 of the source identifies the XY Hamiltonian with the direct sum of $W(G_s)I/2-A(F_j(G_s))$. Here $W(G_s)=5s^2$. The block at $j=k$ consequently gives

$$\lambda_{\max}(H^{XY}(G_s))\ge\frac{5s^2}{2}-R_s>\frac{5s^2+4s^2+5s/2}{2}.$$

Thus the unconditional inequality displayed in Corollary 12 fails too. At $s=40$ the lower bound is $1442912/199>7250$, with gap $162/199$. The source's implication from Conjecture 7 to Corollary 12 remains logically valid. Its conditional $3/4$ and $0.712$ approximation claims lose this premise; their ratios themselves remain open here. The source's other token-graph conjectures are separate statements and are not refuted by this settlement.

**Surviving statements and boundary.** The symbolic counting identity, Rayleigh principle, affine cut bound and unit-weight matching bound remain valid. The experiment computes that the conjectured spectral bound holds at $s=2,k=5$. For even $2\le s\le38$ it checks only that this phase vector does not violate the bound. The full spectral statement throughout $s<40$, odd block sizes, other graph families and repaired upper bounds remain open.

## ASSUMED-UNVERIFIED

Global absence of an earlier settlement or a journal version beyond the source and literature scope recorded in #15417 is unverified. The uniform family and XY consequence have the prose proofs above; they are not claimed as general Lean declarations. Numerical spectral readings have only their stated finite scopes and tolerances.
