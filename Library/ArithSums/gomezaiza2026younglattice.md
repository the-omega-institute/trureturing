---
bibkey: gomezaiza2026younglattice
authors: Ricardo Gómez-Aíza
year: 2026
title: Young-lattice diagonals and a doubly graded multiple-zeta decomposition of $e^\gamma$
doi: null
url: https://arxiv.org/abs/2608.22561v1
claim: The preprint packages Espinosa--Segovia partition branches by fixed Young-lattice excess and multiple-zeta depth; it supplies a positive combinatorial decomposition of $e^\gamma$, not a Robin or RH proof and not a FIB source map.
strata_touched: []
license: citation-only
triage: anchor
---

# Young-lattice excess and depth

The source is Ricardo Gómez-Aíza, [arXiv:2608.22561v1](https://arxiv.org/pdf/2608.22561v1), submitted 23 August 2026. The inspected PDF has SHA-256 709e095dc39c5134769cd36739faec517490f12136998a5a85de71758137ce8b. This card records the stated generating functions and asymptotic interfaces; the source was not independently formalized here.

For the Espinosa sums

$$
E_{i,j}(n)=
\sum_{\substack{\mu\vdash j\\\ell(\mu)=i}}
\frac{m_\mu(1,1/2,\ldots,1/n)}{\mu_1!\cdots\mu_i!},
$$

the fixed branch is the fixed excess \(j-i=r-1\):

$$
A_r(n)=\sum_i\log(i+r)E_{i,i+r-1}(n).
$$

The finite product

$$
F_n(u,v)=\prod_{q=1}^n\left(1+v(e^{u/q}-1)\right)
$$

has coefficient \([u^jv^i]F_n=E_{i,j}(n)\), as in the source’s equation (1). After replacing \(v\) by \(z/u\), the coefficient of \(u^{r-1}\) collects the whole fixed-excess diagonal, so the non-hook terms are indexed by partitions of \(r-1\), rather than treated as unrelated exceptions.

The limiting product

$$
H(u)=\prod_{q\ge1}\frac{q}{q+1}
\left(1+\frac{e^{u/q}-1}{u}\right)
$$

gives \(A_r(n)\sim C_r n\log\log n\) for fixed \(r\), with \(C_r=[u^{r-1}]H(u)\). The one-part coefficient is Segovia's hook constant, while \(C_r\) is the sum of positive coefficients \(C_\nu\) over all partitions \(\nu\vdash r-1\). A second variable records the number \(d=\ell(\nu)\) of non-unit rows:

$$
H(u,y)=\prod_{q\ge1}
\left[1+y\frac{q(e^{u/q}-1)-u}{u(q+1)}\right],
\qquad
C_{r,d}=[u^{r-1}y^d]H(u,y).
$$

The row sums recover the fixed-excess constants \(C_r\); column sums recover the fixed-depth blocks in an Abel-regularized multiple-zeta expansion. At \(u=y=1\), the positive coefficient array gives the bookkeeping identity

$$
e^\gamma=1+\sum_{r\ge2}\sum_{d=1}^{r-1}C_{r,d}
=1+\sum_{d\ge1}\sum_{r\ge d+1}C_{r,d}.
$$

The source explicitly treats this as a combinatorial/asymptotic organization, not as progress toward RH.

## Boundary for the FIB route

The two indices here have a precise meaning—Young-lattice excess and non-unit-row depth—but neither is a Fibonacci rank, a five-window state, a Zeckendorf tail state, or a prime-exponent count. The product is built from the additive reciprocal alphabet \(1/q\); the FIB source uses an additive composition address and its ordinary integer readout. No map in the source transports a FIB address to the divisor subset or partition family used by \(A_r(n)\). Reusing \(C_{r,d}\) for Robin therefore requires a new common-source theorem, not a relabeling of \(r\) or \(d\).

There is, however, one exact interface that is useful for the current budget analysis. For an integer \(N\) with ordered divisors \(1=d_1<\cdots<d_{\tau(N)}=N\), any branch cutoff \(D_r(N)=d_j\) satisfies

$$
Z(N)=\sum_{d_i\le D_r(N)}\frac1{d_i}
   +\sum_{d_i>D_r(N)}\frac1{d_i}.
$$

The first term is the realized branch prefix and the second is a nonnegative divisor tail. Thus a FIB-to-branch map would have to control this tail at the same \(N\); the positive array identity for \(e^\gamma\) does not supply that pointwise control. This is the standard finite-sum decomposition applied to the proposed source map, not new mathematical content; the branch construction and its asymptotics are cited literature results.

The source's fixed-\(r\) limits are not uniform in \(r\), and its Abel-regularized depth identity is not an Euler-price or floor-residual estimate. It therefore does not close the current missing implication

$$
\text{FIB address}
\Longrightarrow
\text{CA/SA source with a signed Robin margin}.
$$

The five labels of a single FIB window cannot injectively encode the seven
partition shapes of excess five. This is only a cardinality obstruction to
that single-window identification; it leaves multiwindow encodings and
aggregation maps undecided. Neither this elementary check nor the finite-sum
decomposition is a new partition or Robin theorem.
