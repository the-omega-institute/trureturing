---
slug: monbroussou-et-al-2025-hamming-weight-pattern-spectral-gap
bibkey: monbroussouetal2025hammingweight
doi: 10.22331/q-2025-05-15-1745
url: https://arxiv.org/abs/2309.15547v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.result
---

# Connected Hamming-weight gate patterns have an inverse-polynomial spectral gap

## Problem

L. Monbroussou, E. Z. Mamon, J. Landman, A. B. Grilo, R. Kukla and E. Kashefi, *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*, Quantum 9, 1745 (2025), DOI 10.22331/q-2025-05-15-1745; arXiv:2309.15547v4, Conjecture `conj:spectral-gap`, `Quantum.tex` lines 1980–1985:

> Let $(U_{0,n})_{n\geq2}$ be a sequence of connected patterns of RBS/FBS gates (\cref{def:connected-pattern}), where each $U_{0,n}$ is such a pattern over $n$ qubits.
> If the number $J_n$ of gates in the pattern $U_{0,n}$ satisfies $J_n \in \mathcal{O}\left(\mathrm{poly}(n)\right)$, then for any fixed Hamming weight $k \in \mathcal{O}(1)$, the associated $d_{k,n} \times d_{k,n}$ stochastic matrix $T_n:=T^{(U_{0,n}^k)}$ (\cref{eq:stochastic-matrix-T-def}) satisfies
>
> $\Delta_n \in \Omega\left(1/\mathrm{poly}(n)\right)\,,$
>
> where $\Delta_n:=1-|\lambda_2(T_n)|$ denotes the spectral gap of the stochastic matrix $T_n$.

The versioned arXiv source archive contains `Quantum.tex` (2252 lines, md5 `057c1aeb9e7f5c3b57445d20f924f4fc`). Its line 1975 states: “The actual proof of \cref{conj:spectral-gap} is left for future work.”

Here $X_{n,k}=\{A\subseteq\mathrm{Fin}\,n:|A|=k\}$ is the weight-$k$ basis, with $N=\binom nk$. A gate on distinct qubits $a,b$ exchanges their labels by $\tau_{ab}$ and has stochastic matrix $P_{ab}=(I+S_{ab})/2$, where $S_{ab}$ is the permutation matrix on $X_{n,k}$ induced by $\tau_{ab}$. A configuration containing both labels or neither is fixed. The pattern matrix is $T=P_J\cdots P_1$, with its first listed gate acting first. The source defines these matrices by squaring the RBS/FBS entries at angle $\pi/4$ (lines 158–192, 1455–1458 and 1486–1489), and its gap by the second-largest eigenvalue modulus (lines 1397–1405).

Issue [#22140](https://github.com/the-omega-institute/trureturing/issues/22140) fixes the nontrivial sectors $1\le k<n$ and the sum-zero complex eigenvector formulation stated below. This formulation is proved. The source correspondence is described in [the literature note](../Library/Eigenstructure/monbroussouetal2025hammingweight.md).

## Motivation

For connected periodic structure ansätze, the source relates gradient variances to powers of these stochastic matrices. At fixed Hamming weight, an inverse-polynomial gap makes its required repetition scale $\Delta_n^{-1}\binom nk n$ polynomial. The source explicitly identifies the conjecture as a premise of its polynomial-depth absence-of-barren-plateaus conclusion (lines 503–504, 1975 and 2021–2030).

## Gap

Issue #22140 records the bounded literature check before any Lean:

- The orchestrator read the v4 TeX, searched for spectral gaps of RBS/FBS and Hamming-weight-preserving stochastic matrices, and found the source and unrelated random-circuit gap results.
- The orchestrator's repository search found no existing record of arXiv:2309.15547 or arXiv:2606.14822.
- The search seat reported the conjecture as Conjecture 9.1 of Monbroussou, arXiv:2606.14822v1; it reported 39 citing records on the Quantum page and no settlement in the checked follow-ups arXiv:2510.02430, 2508.14470, 2609.01303, 2606.26873, 2607.24728 and 2608.01194.
- The search seat reported no match in MathDB or formal-conjectures.

`not-found-in-searched-scope`.

## Route

For natural numbers $n,k$, let $X=X_{n,k}$, $N=|X|$, and let a pattern be a finite list of pairs in $\mathrm{Fin}\,n$. Write $J$ for its length. All vector norms below are Euclidean norms on $\mathbb C^X$, and real matrices act on complex vectors by entrywise complexification. Put $E(v)=\sum_{e\in\mathrm{pat}}\|v-P_ev\|^2$, with list multiplicities retained; this is `staticEnergy`.

1. **Gate action and energy loss.** For arbitrary $n,k$, qubit labels $a,b$, and $v\in\mathbb C^X$, `gate_apply` identifies the gate matrix action with `average`, the midpoint of $v$ and its coordinate permutation; `pattern_apply` identifies the ordered matrix product with `run` for every pattern and vector. For any finite index type, any permutation of it and any complex Euclidean vector, `projection_energy` gives $\|Pv\|^2+\|v-Pv\|^2=\|v\|^2$, where $P$ is that midpoint operator. Consequently, for every pattern and vector, `increments_energy` identifies the sum of squared successive changes with $\|v\|^2-\|Tv\|^2$, and `energy_control` proves $E(v)\le J^2(\|v\|^2-\|Tv\|^2)$.
2. **Connectivity and Poincaré estimate.** Under `connectedPattern pat`, meaning that every gate has distinct endpoints and the qubit graph is connected, `configuration_connected` proves that the configuration graph is preconnected: any two configurations are reachable. It uses `EdgeTranspositionGeneration.connected_edge_transpositions_generate` on the finite connected qubit graph and the transitivity of permutations on equal-cardinality subsets. For the same connected pattern and any $v\in\mathbb C^X$ with $\sum_Av_A=0$, `poincare_bound` proves $\|v\|^2\le N^2E(v)$.
3. **A bound for an individual eigenpair.** For $n\ge2$, a pattern satisfying `connectedPattern`, $\mu\in\mathbb C$, and $v\in\mathbb C^X$ satisfying $v\ne0$, $\sum_Av_A=0$ and $Tv=\mu v$, `spectral_core` proves $|\mu|\le1-1/(2J^2N^2)$. Here `pattern_length_pos`, under $n\ge2$ and `connectedPattern`, supplies $J>0$, and the nonzero coordinate of $v$ supplies $N>0$, so the divisions have positive denominators.
4. **Uniform polynomial witnesses.** For all natural $n,k$, `config_card_le` gives $N\le n^k$. For natural $k,c,a$ and a family with `connectedPattern (pat n)` and $J_n\le c n^a$ for every $n\ge2$, `polynomial_gap` proves, for every $n>k$ with $n\ge2$ and every eigenpair satisfying the nonzero and sum-zero conditions of step 3, $|\mu|\le1-d/n^b$ with $d=1/(2\max(c,1)^2)$ and $b=2a+2k$. Under the additional hypothesis $k\ge1$ of `claim`, `result` supplies these witnesses and proves $d>0$.

## Falsifier

The proof would not settle the source question if the configurations, connectivity or ordered gate product differed from the source's. The correspondence uses:

- `Choice n k`, exactly the $k$-element subsets of $\mathrm{Fin}\,n$;
- `swapConfig` and `gateMatrix`, giving the squared RBS/FBS entries at $\pi/4$, with the fermionic signs removed by squaring and diagonal entry one on fixed configurations;
- `patternMatrix`, the reverse list product $P_J\cdots P_1$;
- `qubitGraph`, with an undirected edge for either orientation of a gate, and `connectedPattern`, requiring distinct endpoints and connectivity, corresponding to the source's arrows in both directions (lines 1631–1640).

No normality or diagonalizability of the product is assumed. The compiled claim bounds eigenpairs directly; the identification with the source's second-largest-modulus gap is an argument under “What the settlement shows”, not a separately formalized spectral-gap definition.

## Evidence

The canonical source is `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.lean` (551 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.lean.json`, statement `sha256:803de58954cd844881211dbc3dbbafce38ec0c2ed850de8a6802b8ca062572c2`.

Declaration statements:

- `result`: `sha256:1e84a67fc07ab6ca3120d31eea767c6e67613bff9c6adffa5d2e03e9e0057055`;
- `claim`: `sha256:7e31d592c883fb5a032871754b2a83e1fd520ed9c10533e0b9d65ad79151d5c1`.

## Triage

Tier 1 conjecture of a 2025 journal article, preregistered in issue #22140 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $k,c,a$ with $k\ge1$, and every family of gate lists on $n$ qubits whose lists have distinct gate endpoints, connected qubit graphs and lengths at most $c n^a$ for every $n\ge2$, there exist a real $d>0$ and a natural $b$ such that, for every $n>k$ with $n\ge2$, every $\mu\in\mathbb C$ and nonzero $v:X_{n,k}\to\mathbb C$ with $\sum_Av_A=0$ and $T_nv=\mu v$ satisfy $|\mu|\le1-d/n^b$.

**Computed, not formalized** (orchestrator, recorded in #22140): for the tested family of 162 random connected patterns with $3\le n\le8$ and $1\le k<n$, a violation of $|\lambda_2(T)|\le1-\mu_2(L)/(2J^2)$ was not observed, where $L=\sum_j(I-P_j)$ and $\mu_2(L)$ is its smallest nonzero eigenvalue.

**Argued, not formalized.**

- *Decisive mechanism.* For $n\ge2$, a pattern satisfying `connectedPattern`, and a nonzero sum-zero complex eigenvector $v$ with $Tv=\mu v$, `spectral_core` combines the configuration-graph estimate with the ordered-product energy loss. The estimate requires neither commutation of the gates nor normality of their product, so a nonsymmetric product presents no additional spectral assumption.
- *The source's gap.* Every gate permutation fixes the constant vector and preserves the coordinate sum, as does its average with the identity and every product of those averages. Thus $\mathbb C^X$ splits into the invariant constants and the invariant sum-zero subspace. For $1\le k<n$, there are at least two configurations, obtained by exchanging an occupied and an unoccupied label, so the sum-zero subspace has positive dimension. Over $\mathbb C$ its finite-dimensional operator has eigenvalues; the bound on all its eigenvectors places all of them strictly inside the unit circle. In this invariant direct sum the remaining block is the single constant eigenvalue $1$, so the source's second-largest eigenvalue modulus has the same bound, without a diagonalizability assumption.
- *Connectivity is essential.* For $n\ge2$, $k=1$ and a disconnected qubit graph, take a nonempty proper component $C$. The vector equal to $n-|C|$ on $C$ and $-|C|$ outside $C$ is nonzero and has sum zero. Every gate swaps labels within components, so every gate average fixes this vector and the product has a sum-zero eigenvector with eigenvalue $1$.
- *A complementary range.* For $0\le k\le n$, complementation is a bijection between the weight-$k$ and weight-$(n-k)$ configurations and commutes with every label transposition. Its permutation matrix therefore intertwines every gate and their ordered products, giving equal spectra in the two sectors. This transfers the gap estimate to a fixed number of unoccupied qubits; the complement correspondence is not formalized in this module.
- *Sharpness and neighbouring questions.* For $n=2$, $k=1$ and a single gate, the two-by-two matrix has every entry $1/2$, with eigenvectors $(1,1)$ and $(1,-1)$ of eigenvalues $1$ and $0$, respectively. Its gap is therefore $1$, while the local estimate gives only $1/8$. Optimal worst-case dependence on gate count and weight is open here. The result also leaves open here a uniform inverse-polynomial bound in general growing-weight regimes, the source's suggestion of weight independence or exponentially small differences between weights (line 2114), and its proposed comparison with approximate unitary $2$-designs (line 2164).
- *Effect on the paper.* Using the source-gap correspondence above, the witnesses in `polynomial_gap`, under its connected-family and $J_n\le c n^a$ assumptions, give $\Delta_n^{-1}\binom nk n=O(n^{2a+3k+1})$ for fixed $k\ge1$ and $n>k$. Hence a sufficiently large polynomial choice of repetitions $L_n$, with $l_n=\lfloor\alpha L_n\rfloor$ and fixed $0<\alpha<1$, meets the source's requirement that $L_n$, $l_n$ and $L_n-l_n$ are all of order at least $\Delta_n^{-1}\binom nk n$. This supplies the conjectural gap premise of the source's `thm:concluding-back-to-variance` and its informal `thm:NoBPPSA`. Their gradient-variance conclusions still use the source's other results and assumptions: normalized real input and target states of weight $k$, circuit angles jointly uniform on $[0,2\pi]^D$ for a circuit of $D$ gates, and the squared Euclidean distance from the final state to the target as cost. Those conclusions are not Lean theorems of this module.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches reported in #22140 and does not establish exhaustive worldwide novelty or priority. The reported thesis reading, citation count, follow-up checks and database searches were not independently reproduced here. The orchestrator's 162-pattern numerical check and the source's numerical experiments were not rerun.

The identification of the source's RBS/FBS matrices and bidirectional graph with the Lean definitions is a source-reading argument. The statements in “Argued, not formalized”, including the spectral-gap interpretation, disconnected-pattern obstruction, complement correspondence, sharpness example and consequences for gradient variances, are not formalized. The source's remaining stochastic-convergence and variance arguments were read in the cited passages but not independently verified in full. Optimal bounds, general growing-weight bounds, weight independence and the comparison with approximate unitary $2$-designs remain open here.
