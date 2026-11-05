---
bibkey: bailey2024orthogonalpst
authors: Rachel Bailey
year: 2024
title: "Orthogonal polynomials and perfect state transfer"
doi: 10.1098/rsta.2024.0414
url: https://arxiv.org/abs/2412.16351v1
claim: "A review of orthogonal polynomials, Jacobi matrices and perfect state transfer on weighted paths, which restates that endpoint PST implies PST between mirror interior vertices and lists as open whether the converse holds for arbitrary Jacobi matrices."
strata_touched:
  - D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation
license: citation-only
triage: anchor
---

# Orthogonal polynomials and perfect state transfer

R. Bailey, arXiv:2412.16351v1 [quant-ph, math-ph]; Phil. Trans. R. Soc. A 383 (2025). Quotations are from the v1 TeX source.

Jacobi matrices:

> Given an $N\times N$ Jacobi matrix $J$, … with $a_n\neq 0, n \geq 0$, one may associate to it a family of orthonormal polynomials

(the matrix has diagonal $b_0,\dots,b_{N-1}$ and off-diagonal $a_0,\dots,a_{N-2}$).

Perfect state transfer:

> Let $j$ and $k$ be vertices of a finite graph and $J$ be its adjacency matrix. Then \textit{perfect state transfer (PST)} from vertex $n$ to vertex $m$ occurs if there exists some time $t_0>0$ such that \[\left|{\bf e}^{\top}_m\exp(it_0J){\bf e}_n\right|^2=1.\]

The proposition of Kirkland et al. that it restates:

> For a weighted path of length $N$ with or without potentials, PST between vertices 1 and $N$ implies PST between vertices $j$ and $N+1-j$ for each $j=2, \dots, N-1$. If for some $2\leq j \leq N-1$, there is PST between vertices $j$ and $N+1-j$, and if in addition none of the eigenvectors of the Hamiltonian has a zero entry in the $j$-th position, then the converse holds.

The open question (Section "Open Questions"):

> Recall Proposition \ref{prop:kirkland}, which states that PST between end vertices implies PST between opposite interior vertices. The converse to the statement is only proven for graphs with Hamiltonians which have eigenvectors of a specific type. Thus, it remains an open question as to if the converse holds for arbitrary Jacobi matrices.

The question originates in Kirkland, McLaren, Pereira, Plosker and Zhang (`Library/GraphInvariants/kirkland2019rationalweightspst.md`).

## Verified locator

Source: https://arxiv.org/abs/2412.16351v1
- URL: https://arxiv.org/abs/2412.16351v1 (source `new.tex`, md5 `14bb6ec91f65ed9f5412b41efb2d5b5a`):
  - Jacobi matrices, l. 184–195;
  - perfect state transfer, l. 318–319;
  - the restated proposition, l. 425–427;
  - the open question, l. 602.
- DOI: 10.1098/rsta.2024.0414 (https://doi.org/10.1098/rsta.2024.0414; Crossref lists Philosophical Transactions of the Royal Society A, volume 383, issued 9 October 2025; arXiv lists only v1 of 20 December 2024).
