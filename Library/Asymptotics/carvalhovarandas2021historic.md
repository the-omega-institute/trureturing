---
bibkey: carvalhovarandas2021historic
authors: Maria Carvalho; Paulo Varandas
year: 2021
title: Genericity of historic behavior for maps and flows
doi: 10.48550/arXiv.2107.01200
url: https://arxiv.org/html/2107.01200v1
claim: Theorem A gives a Baire residual irregular set when the upper Birkhoff average has distinct constant values on two dense subsets of a compact metric dynamical system.
strata_touched:
  - D5/S3/Topology/SeparatedLimsupMeagre
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Asymptotics/carvalhovarandas2021historic -->
# Dense upper-average classes and historic behavior

The primary source is arXiv:2107.01200v1, Section 2, Theorem A,
with the upper-average function defined in equation (2.3) and the
observable irregular set defined in equation (2.2). The v1 version is
dated 2 July 2021. Section 3 supplies the category mechanism for
sequences of continuous observables.

Theorem A assumes a compact metric space X, a continuous map f:X to X,
and a continuous real observable phi. Write
U(n,x) = (1/n) sum over 0 <= j < n of phi(f^[j](x)) for positive n.
If limsup U(n,x) is constant with distinct values on two dense subsets,
the set of points where these averages do not converge is Baire residual.

The formal theorem `separated_limsup_isMeagre` concerns an arbitrary
sequence of continuous real functions on an arbitrary topological space,
in an arbitrary universe. Its conclusion is meagreness of the locus
where the sequence converges to a real number. It has no Baire,
compactness, metrizability, dynamics, or boundedness hypothesis. The
default real `Filter.limsup` is retained. Two-sided bounds are derived
inside each fixed-gap closed tail set before conditionally complete
order lemmas are used.

This arbitrary-sequence extension is the present derivation of the
source's category argument. It is not quoted as the verbatim theorem of
the paper, and no originality claim is made. In a Baire space,
`dense_of_mem_residual` gives density of the complementary divergence
set. For Theorem A, finite sums and continuity of iterates show that the
actual Birkhoff averages are continuous. The n=0 value is zero, using the
empty sum and real inverse of zero; a single initial term affects neither
convergence nor limsup. Compact metric spaces are Baire. The conclusions
then apply directly to those averages.

This is a citation of mathematical ideas and statements. No external
Lean code is incorporated.
