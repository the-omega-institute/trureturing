---
bibkey: lanczos1950iteration
authors: Cornelius Lanczos
year: 1950
title: An Iteration Method for the Solution of the Eigenvalue Problem of Linear Differential and Integral Operators
doi: null
url: https://nvlpubs.nist.gov/nistpubs/jres/045/jresv45n4p255_A1b.pdf
claim: Krylov orthogonal recurrence specializes to symmetric tridiagonal reduction; the response application uses an explicitly normalized exact-arithmetic convention.
strata_touched: []
license: citation-only
triage: anchor
---

# Symmetric tridiagonal recurrence

The primary publication is *Journal of Research of the National Bureau of
Standards* 45(4), 255–282, Research Paper RP2133.
[Sections VII–VIII](https://nvlpubs.nist.gov/nistpubs/jres/045/jresv45n4p255_A1b.pdf?download=2),
pp. 267–270, equations (77)–(78) and the symmetric specialization (97),
supply the orthogonal recurrence and tridiagonal reduction. The paper's
coefficient conventions are not identical to the normalized convention below.

[The Static endpoint application, Theorem 29.8](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)
uses $q_{-1}=0$, $\beta_0=0$, $q_0=b/\|b\|$ only when $b\ne0$.
The residual norm defines $\beta_{j+1}$ and is normalized only when
nonzero. First breakdown $\beta_q=0$ means that $q$ directions span the
cyclic subspace. A zero port has dimension zero with no starting direction.
For the specified diagonal-three endpoint chain,
$q_j=(-1)^je_{j+1}$, $\alpha_j=3$, $\beta_j=1$ for $1\le j<n$,
and $\beta_0=\beta_n=0$. The continued fraction uses squared off-diagonals.

These are exact-arithmetic and supplied-port statements. Finite-precision
breakdown, loss of orthogonality, numerical stopping and noisy observation
require additional analysis. The Jacobi chain represents the same linear
response; it does not supply native FIB arithmetic operations.
