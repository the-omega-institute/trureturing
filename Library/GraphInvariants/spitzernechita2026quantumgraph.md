---
bibkey: spitzernechita2026quantumgraph
authors: Gian Luca Spitzer; Ion Nechita
year: 2026
title: "Quantum Graph Theory by Example"
doi: 10.22331/q-2026-10-06-2228
url: https://arxiv.org/abs/2603.23651v3
claim: "The paper studies quantum graphs on M_n invariant under diagonal unitary and orthogonal groups, describes the graphs X_{A,B,C} through strange graphs whose edges are classical or carry a phase, proves that X_{A,B,C} has at least as many connected components as its strange graph and that connectedness agrees for n at least 3, and asks for the exact number of connected components of X_{A,·,C} in terms of the strange graph, in particular the role of isolated strange edges with phase π."
strata_touched:
  - D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount
license: citation-only
triage: anchor
---

# Quantum Graph Theory by Example

G. L. Spitzer and I. Nechita, arXiv:2603.23651v3 [math.OA, cross-listed math-ph, quant-ph]; Quantum 10, 2228 (2026). Quotations are from the v3 TeX source.

Connected components (`content/prelims.tex`):

> \begin{definition}
>   A quantum graph $G$ has (at least) $k$ \emph{connected components} if there exist projectors $P_1, \dots, P_k$ on $\C^n$ with $\sum_s P_s = \identity$ such that
>   \begin{equation*}
>     \diagram{conn-comp-condition-mn}
>   \end{equation*}
>   for all $s \neq t$.
> \end{definition}

Strange graphs (`content/groupactions.tex`):

> \begin{definition}[Strange Graphs]
>   Let $G$ be an undirected quantum graph on $M_n$ of the form $X_{A, B, C}$. The \emph{strange graph} $\mathfrak{G}(A, C)$ associated to $G$ is an undirected graph with vertex set $[n]$ and edge set $E \cup \bigcup_{\theta \in [0, 2\pi)}\tilde{E}_\theta$, where
>   \begin{equation*}
>     E = \{ \{i, j\} \subseteq [n] \mid X_{ij} = \identity \} \qquad\&\qquad \tilde{E}_\theta = \{\{i, j\} \subseteq [n] \mid i < j, X_{ij} = \frac{1}{2}\begin{pmatrix}
>         1 & e^{\theta i} \\
>         e^{-\theta i} & 1
>     \end{pmatrix}\}.
>   \end{equation*}
> \end{definition}

The doubling example (`content/graphtheory/conncomp.tex`):

> \begin{proposition}\label{prop:conncompcounterex}
>   For every even $n \in \N$ there exists a quantum graph on $M_n$ of the form $X_{A, \ccdot, C}$ such that $X_{A, \ccdot, C}$ has twice as many connected components as $\mathfrak{G}(A, C)$.
>   \begin{proof}
>     Consider the strange graph obtained by taking the disjoint union of $n / 2$ strange edges with phase $\pi$. The strange graph has $n/2$ connected components, while by \cref{lem:conncompsofdisjunion}, the corresponding quantum graph has $n$ connected components.
>   \end{proof}
> \end{proposition}
>
> However, if $n \geq 3$ then we can still recover the equivalence for the question of connectedness. To show this, we first prove the following lemma, which might be interesting in its own right.

The question (`content/conclusion.tex`):

> It would be interesting to determine the exact number of connected components of $X_{A, \ccdot, C}$ in terms of $\mathfrak{G}(A, C)$, and in particular to understand the role played by isolated strange edges with phase $\pi$.

## Verified locator

Source: https://arxiv.org/abs/2603.23651v3
- URL: https://arxiv.org/abs/2603.23651v3 (v1 24 March, v2 20 September, v3 2 October 2026); TeX sources:
  - `content/prelims.tex` (md5 `129eae25694a4c08a10237cf3a7a50ee`): operator spaces and realignment, l. 170–177; connected components, l. 253–259;
  - `content/groupactions.tex` (md5 `3c0a760c90a0c83bf2947ed6348620cb`): the quantum-graph conditions for $X_{A,B,C}$, l. 152–175; trivial matrices and $X_{A,\cdot,C}$, l. 243–249; strange graphs, l. 419–427;
  - `content/graphtheory/conncomp.tex` (md5 `5d05d0b289afc8bd23de44a5f1190d43`): the doubling example, l. 247–254;
  - `content/conclusion.tex` (md5 `5368d2c066a050b58ed79201d3f39cd3`): the question, l. 8.
- DOI: 10.22331/q-2026-10-06-2228 (https://doi.org/10.22331/q-2026-10-06-2228; Quantum 10, 2228).
