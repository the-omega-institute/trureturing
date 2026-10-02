---
bibkey: wu2014randomized
authors: Jun-Yi Wu; Matteo Rossi; Hermann Kampermann; Simone Severini; Leong Chuan Kwek; Chiara Macchiavello; Dagmar Bruß
year: 2014
title: "Randomized Graph States and their Entanglement Properties"
doi: 10.1103/PhysRevA.89.052335
url: https://arxiv.org/abs/1403.3828v3
claim: "For a graph G and a probability p, the randomized graph state is rho_G^p = sum over spanning subgraphs F of G of p^|E_F| (1-p)^(|E_G| - |E_F|) |F><F|, where |F> = prod over the edges of F of CZ |+>^n is the graph state of F. Section V defines the negativity N(rho_AB) = (||rho_AB^Gamma_A|| - 1)/2 with the trace norm ||X|| = Tr sqrt(X^dagger X), reports numerically that it is monotone in p for the complete graphs K_n and the star graphs S_n with n <= 4, and states that it is an open question whether the monotonic behaviour of the negativity in p is a common feature to all randomized graph states."
strata_touched:
  - D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation
license: citation-only
triage: anchor
---

# Randomized Graph States and their Entanglement Properties

Jun-Yi Wu, Matteo Rossi, Hermann Kampermann, Simone Severini, Leong Chuan
Kwek, Chiara Macchiavello, Dagmar Bruß, Phys. Rev. A 89, 052335 (2014),
arXiv:1403.3828v3 (quant-ph). Quotations are from the arXiv v3 source, with
its macros kept as printed.

The graph state (Section II C):

> $|G\rangle :=\prod_{\{i_{1},i_{2}\}\in E}(\text{CZ})_{i_{1}i_{2}}|+\rangle^{\otimes n}.$

with $\mathrm{CZ}=\mathrm{diag}(1,1,1,-1)$ in the computational basis.

The randomized graph state (Section III, Definition of the randomization
operator):

> $R_{p}(|G\rangle ):=\sum_{F \emph{spans} G}p^{|E_{F}|}\left( 1-p\right)^{\left\vert E_{G}\backslash E_{F}\right\vert }|F\rangle \langle F|,$

> where $F$ are spanning subgraphs of $G$, $E_{F}$ and $E_{G}$ are the sets of

edges of $F$ and $G$; the randomized graph state is
$\rho_G^p:=R_p(|G\rangle)$.

The negativity (Section V):

> We finally quantify the amount of bipartite entanglement by considering the negativity, evaluated with respect to all possible bipartitions of the qubits. The \emph{negativity} of a bipartite state $\rho_{AB}$ is defined \cite{VidalWerner2002-02} as $N(\rho_{AB})=\frac{||\rho_{AB}^{\Gamma_{A}}||-1}{2},$ where $\Gamma_{A}$ represents the partial transposition with respect to the subsystem $A$, and $||X||=\text{Tr}[\sqrt{X^{\dagger}X}]$ is the trace norm.

The open question (Section V, last paragraph):

> We have evaluated the negativity numerically for some RG states composed of a small number of qubits. The results for the negativity of states corresponding to the complete graph $K_{n}$ and the star graph $S_{n}$ up to $n=4 $ vertices are reported in Fig. \ref{fig::monotomicity_of_negativity}. As can be seen, in the studied cases the negativity exhibits a monotonic behaviour in terms of the randomness parameter $p$. This suggests that the entanglement content might increase monotonically in $p$ with respect to any bipartition. Actually, since for the extreme cases $p=0$ and $p=1$ we have a fully separable state and an entangled state, respectively, one might expect that, as the weight of entangled subgraph states in $\rho^{p}_{G}$ increases with increasing $p$, a corresponding growth of the entanglement content of the RG state $\rho^{p}_{G}$. However, even though this conjecture is supported by numerical evidence, it is an open question whether the monotonic behavior of the negativity in terms of the randomness $p$ is a common feature to all RG states.

The encoding indexes the qubits by `Fin n` and the computational basis by
`Fin n → Fin 2`, takes the graph state of an edge set to be its CZ phases
times $|+\rangle^{\otimes n}$, sums over the subsets of the edge set of $G$,
and uses the frozen trace norm $\operatorname{re}\operatorname{Tr}
\sqrt{X^\dagger X}$.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.89.052335 (Phys. Rev. A 89,
  052335, 2014).
- URL: https://arxiv.org/abs/1403.3828v3 (v3, 2014-06-03, the latest
  version, marked as the published version; source
  `Random_graph_states_and_their_entanglement_properties_published.tex`,
  md5 `3c212afcc2a0e40f0e7a9b4a2082292e`): the graph state (l. 262–267),
  the randomization operator (l. 328–336), the negativity (l. 632–640) and
  the open question (l. 644–657).
