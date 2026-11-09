---
bibkey: alfuraidan2026laplacian
authors: Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra
year: 2026
title: "Metric dimension and maximum eigenvalue multiplicity of graph Laplacians"
doi: 10.48550/arXiv.2610.26875
url: https://arxiv.org/abs/2610.26875v1
claim: "Problem 30 asks for infinite connected twin-free graph families satisfying exactly one of mmL(G)=dim(G) and mmQ(G)=dim(G)."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaStructure
  - D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence
  - D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaSeparation
license: citation-only
triage: anchor
---

# Metric dimension and maximum eigenvalue multiplicity of graph Laplacians

## Verified locator

DOI: 10.48550/arXiv.2610.26875

Source: https://arxiv.org/abs/2610.26875v1

The source is arXiv v1. Problem 30 appears on p. 27; maximum multiplicity on
pp. 1–2; distances, eigenspace multiplicity and metric dimension on p. 3;
the two Laplacians and twins on p. 4; theta path parameters on p. 24.

## Source statements

The following TeX passages reproduce the source. The macros rev and revblue
only color their arguments; mm and mult denote the corresponding operators.

### Graphs and distances (p. 3)

```tex
All graphs are finite and simple, and \(G\) is connected unless stated otherwise. We use \(V(G)\) and \(E(G)\) for its vertex and edge sets, and \(|V(G)|\) for its order. For every vertex \(v\), its open neighborhood is \(N(v)=\{u:uv\in E(G)\}\), its closed neighborhood is \(N[v]=N(v)\cup\{v\}\), and its degree is \(\deg_G(v)=|N(v)|\). For every pair of vertices \(u,v\), \(d_G(u,v)\), or \(d(u,v)\) when the graph is clear, is the length of a shortest path between them.
```

### Spectral multiplicity (p. 3)

```tex
For a real symmetric matrix \(M\), \(\Spec(M)\) is its multiset of eigenvalues, and \(\mult_M(\lambda)=\dim\ker(M-\lambda I)\) is the multiplicity of a real number \(\lambda\). It is zero when \(\lambda\) is not an eigenvalue. The notation \(\lambda^{(a)}\) in a spectrum records \(a\) copies of \(\lambda\). An eigenvalue is \emph{simple} when its multiplicity is one, and a spectrum is simple when every eigenvalue is simple. The \emph{nullity} of a matrix is the dimension of its kernel. We write \(I_n\) for the identity matrix, \(M^T\) for the transpose, \(\operatorname{diag}(a_1,\ldots,a_n)\) for a diagonal matrix, and \(\chi_M(z)=\det(zI-M)\) for the characteristic polynomial; the order of an unsubscripted \(I\) is determined by \(M\).
```

### Maximum multiplicity (pp. 1–2)

```tex
\rev{For each choice \(X\in\{L,Q\}\), define the \emph{maximum multiplicity} (abbreviated \(\mm_X\)) by}
\[
\rev{\mm_X}(G)=
\max_{\lambda\in\operatorname{Spec}(X(G))}
\operatorname{mult}_{X(G)}(\lambda).
\]
\rev{Here \(\operatorname{mult}_{X(G)}(\lambda)\) is the dimension of the eigenspace at \(\lambda\). We maximize the multiplicity over all eigenvalues, rather than taking the multiplicity of the largest eigenvalue.}
```

### Metric dimension (p. 3)

```tex
Let
\(
S=\{s_1,\dots,s_t\}\subseteq V(G).
\)
The \emph{distance representation} of a vertex \(v\in V(G)\) with respect to \(S\) is defined by
\(
r(v|S)=
(d(v,s_1),\dots,d(v,s_t)).
\)
The set \(S\) is called a \emph{resolving set} if
\(
r(u|S)\neq r(v|S)
\)
for all distinct vertices \(u,v\in V(G)\).
The \emph{metric dimension} of \(G\), denoted by \(\dim(G)\), is the minimum cardinality of a resolving set.
```

### Laplacians (p. 4)

```tex
The adjacency matrix, degree matrix, Laplacian matrix, and signless Laplacian matrix of a graph \(G\) are denoted by \(A(G)\), \(D(G)\), \(L(G)\), and \(Q(G)\), respectively, where
\(L(G)=D(G)-A(G), \qquad Q(G)=D(G)+A(G).\)
The signless Laplacian matrix and its basic spectral properties are discussed in~\cite{Cvetkovic2007}.


Thus \(\mm_L(G)\) is the largest multiplicity attained by any eigenvalue of \(L(G)\), and \(\mm_Q(G)\) is defined analogously for \(Q(G)\). Neither notation denotes the multiplicity of the largest eigenvalue. Empty indexed families are omitted when taking a maximum.
```

### Twins (p. 4)

```tex
\begin{definition}
Two distinct vertices \(u,v\in V(G)\) are called \emph{twins} if
\(
N(u)\setminus\{v\}=N(v)\setminus\{u\}.
\)
They are called \emph{false twins} if \(uv\notin E(G)\), equivalently
\(N(u)=N(v)\), and \emph{true twins} if \(uv\in E(G)\), equivalently
\(N[u]=N[v]\).

The twin relation, together with equality, is an equivalence relation
on \(V(G)\). Its equivalence classes are called \emph{twin classes}.
\rev{A twin class is \emph{nontrivial} when it contains at least two vertices. The vertices of each such class form either an independent set (a false twin class) or a clique (a true twin class). A graph is \emph{twin-free} when it has no nontrivial twin classes; the twin relation is a relation between vertices.}
\end{definition}
```

### Theta parameters (p. 24)

```tex
\rev{For every \(p,q,r\in\mathbb{Z}_{\geq2}\), construct \(\Theta_{p,q,r}\) from three paths with \(p,q,r\) edges, respectively, by identifying their three initial vertices as one vertex \(u\) and their three terminal vertices as one distinct vertex \(v\). No other vertices are identified, and no additional edges are added. Thus the paths have exactly the two endpoints in common.}
```

### Problem 30 (p. 27)

```tex
\begin{problem}
Do there exist infinite families of connected twin-free graphs satisfying exactly one of the two equalities
\(\rev{\mm_L}(G)=\dim(G),\qquad \rev{\mm_Q}(G)=\dim(G)?\)
The computational census shows that finite twin-free examples occur in both directions.
\end{problem}
```

## Scope of the affirmative construction

The graphs Θ₃,₃,₆ₖ₊₄ for k ≥ 1 have distinct orders 6k+9. The delivered
assertion gives the Laplacian equality and the failure of the signless equality.
It does not assert a second infinite family in the reverse direction or the
full theta classification of Problem 29.

## Literature boundary

The bounded literature screen is recorded in issue #22167. Exhaustive citation
coverage and absence of an independent published resolution are
ASSUMED-UNVERIFIED. The source and its definitions are the cited input; the
theta separating construction is derived in the accompanying Lean modules.
