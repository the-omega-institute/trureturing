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

## Verified locator

- DOI: https://doi.org/10.1080/03081087.2018.1442810
- arXiv: https://arxiv.org/abs/1708.03283v2
