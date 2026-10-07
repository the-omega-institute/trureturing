---
bibkey: vandennest2004graphical
authors: M. Van den Nest, J. Dehaene, B. De Moor
year: 2004
title: "Graphical description of the action of local Clifford transformations on graph states"
doi: 10.1103/PhysRevA.69.022316
url: https://arxiv.org/abs/quant-ph/0308151v2
claim: "Each stabilizer state is equivalent to a graph state under local Clifford operations; in the binary framework a generator matrix is brought to an invertible X-block by local Hadamard operations and its diagonal is cleared by local phase operations."
strata_touched:
  - D5/S3/Quantum/Information/BinaryLagrangianGraphForm
license: citation-only
triage: anchor
---

# Van den Nest, Dehaene and De Moor, local Clifford reduction to graph states

M. Van den Nest, J. Dehaene and B. De Moor, *Graphical description of the action of local
Clifford transformations on graph states*, Phys. Rev. A 69, 022316 (2004),
arXiv:quant-ph/0308151v2.

## Verified locator

DOI: 10.1103/PhysRevA.69.022316.
Primary version: https://arxiv.org/abs/quant-ph/0308151v2. The TeX source
`localcliffgraph.tex` of v2 supplies §III ("Reduction to graph states") and Theorem 1.

## Source statements (§III)

"Theorem 1: Each stabilizer state is equivalent to a graph state under local Clifford
operations."

Proof outline in the binary framework, for a generator matrix $S=\begin{bmatrix}Z\\X\end{bmatrix}$
whose columns span a self-orthogonal subspace for the symplectic form $P$: "The result is
obtained by proving the existence of a local Clifford operation $Q\in C^l$ such that
$QS=\begin{bmatrix}Z'\\X'\end{bmatrix}$ has an invertible lower block $X'$. Then
$S':=QSX'^{-1}=\begin{bmatrix}Z'X'^{-1}\\I\end{bmatrix}$, where $Z'X'^{-1}$ is symmetric from
the property $S'^TPS'=0$; furthermore, the diagonal entries of $Z'X'^{-1}$ can be put to zero by
additionally applying the operation $\begin{bmatrix}1&1\\0&1\end{bmatrix}$ to the appropriate
qubits". The invertible lower block is reached by "a Hadamard transformation
$\begin{bmatrix}0&1\\1&0\end{bmatrix}$ on the qubits $k+1,\dots,n$" after a basis change that
splits $S$ by the rank $k$ of $X$.

## Scope

The paper states the reduction for qubit stabilizer states and notes that it is a special case
of a result of Schlingemann for $d$-level stabilizer codes. It gives an explicit construction of
the Hadamard set from a rank decomposition of the generator matrix.
