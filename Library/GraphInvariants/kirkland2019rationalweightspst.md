---
bibkey: kirkland2019rationalweightspst
authors: S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang
year: 2019
title: "Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials"
doi: 10.1080/03081087.2018.1442810
url: https://arxiv.org/abs/1708.03283v2
claim: "Rational weights conjecture: a weighted path on at least four vertices, with or without potentials, whose edge weights are all rational has no adjacency matrix perfect state transfer between its end vertices at readout time π. Proposition prop:rat proves it for n = 4 and for n ≥ 5 with n ≡ 3 or 5 (mod 8)."
strata_touched:
  - D5/S3/Quantum/Dynamics/RationalWeightPathTransfer
  - D5/S3/Quantum/Dynamics/PathMiddleVertexMoments
  - D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer
license: citation-only
triage: anchor
---

# Perfect state transfer on weighted paths with rational weights

S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang, *Perfect quantum
state transfer in weighted paths with potentials (loops) using orthogonal
polynomials*, arXiv:1708.03283v2 (22 March 2019); Linear and Multilinear
Algebra 67(5) (2019) 1043–1061.

The Hamiltonian of a weighted path on $n$ vertices is the tridiagonal
adjacency matrix with the potentials $q_j$ on the diagonal and the positive
edge weights $r_j$ off the diagonal. The source defines perfect state transfer
verbatim:

> There is \emph{perfect state transfer} from vertex $j$ to vertex $k$ if there exists some time $t=t_0$ such that $|e_j^T e^{it_0H} e_k|^2=1$

The introduction states the conjecture:

> For  XX dynamics, our analysis leads us to propose the following conjecture:  weighted paths on at least four vertices with or without loops must have at least one irrational weight in order to have adjacency matrix PST at a fixed readout time $\pi$; we confirm  this conjecture for $n=4$ as well as for $n\equiv 3\modn 8$ and for $n\equiv 5\modn 8$.

The section "Adjacency Matrices and the Rational weights conjecture" repeats it:

> We have a conjecture about the weights: if all the weights of a weighted path on at least 4 vertices are rational numbers, then there is no adjacency matrix PST at time $\pi$ between the end vertices of the path. We confirm that conjecture in the cases that $n=4$, $n\equiv 5\modn 8$ and for $n\equiv 3\modn 8$ but $n\neq 3$.

Proposition `prop:rat`:

> Suppose that $n=4,$ or $n\geq 5$ and $n\equiv 3\modn 8$ or $n\equiv 5\modn 8$. If the weights of a weighted path on $n$ vertices with or without potentials are all rational numbers, then there is no adjacency matrix PST between its end vertices at readout time $\pi$.

The weights are the edge weights $r_j$; the potentials are unrestricted real
numbers.

The module `D5/S3/Quantum/Dynamics/RationalWeightPathTransfer` proves the
statement of the conjecture for every $n = 2^k + 1$ with $k \ge 1$, in both
directions between the end vertices; the source does not single out this
family. This is partial progress on the conjecture: $k = 1$ gives $n = 3$,
below the conjecture's range $n \ge 4$; $k = 2$ gives $n = 5$, one of the cases
of Proposition `prop:rat`; the new sizes are those with $k \ge 3$, namely
$n = 9, 17, 33, \dots$, which satisfy $n \equiv 1 \pmod 8$ and lie outside the
cases of Proposition `prop:rat`. The odd sizes not of the form $2^k + 1$ and
not congruent to $3$ or $5$ modulo $8$, and the even sizes $n \ge 6$, are not
settled by the source or this module.

Two steps of that proof are recorded by the source as known. Section 2 of the
source cites Kay for the fact that a symmetric tridiagonal Hamiltonian with
perfect state transfer between its end vertices is persymmetric, and recalls
that after a common shift the eigenvalues are then integers that alternate
between even and odd. The module states the first for an arbitrary unitary
commuting with the path Hamiltonian, and derives from the second the identity
$P\sum_{i\in A} 1/\prod_{j\ne i}(z_i - z_j) = 1/2$ for the spectral class $A$
of a Hermitian matrix; the 2-adic valuation of that sum is the module's own
step.

The module `D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer`, with the
spectral weights and integer moments at the middle vertex of
`D5/S3/Quantum/Dynamics/PathMiddleVertexMoments`, proves the statement of the
conjecture for every odd $n = 2m + 1 \ge 3$, in both directions between the
end vertices and with arbitrary real potentials: $n = 3$ lies below the
conjecture's range, the sizes $n \equiv 3, 5 \pmod 8$ are the cases of
Proposition `prop:rat`, and the sizes $n \equiv 1, 7 \pmod 8$ lie outside
those cases. The even sizes $n \ge 6$ are not settled by the source or these
modules. The source obtains its odd cases from the weight next to the middle
vertex: with $S_1=\sum_{r=1}^n(-1)^{r+n}\alpha_r$ and
$S_2=\sum_{r=1}^n(-1)^{r+n}\alpha_r^2$ for the ordered eigenvalues
$\alpha_r$, its Corollary `cor:middle` gives, for $n$ odd,
$r_{\frac{n-1}2}=\frac{\sqrt{S_2-S_1^2}}2$ and $q_{\frac{n+1}2}=S_1$; it also
recalls, citing Cantoni and Butler, that the eigenvectors of a mirror-symmetric
Hamiltonian are symmetric or antisymmetric. The modules use the diagonal
entries of all the powers of the Hamiltonian at the middle vertex and the
Hankel determinants of these moments of every size up to $m + 1$.

## Verified locator

- DOI: https://doi.org/10.1080/03081087.2018.1442810
- arXiv: https://arxiv.org/abs/1708.03283v2
