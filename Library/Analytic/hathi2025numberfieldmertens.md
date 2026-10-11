---
bibkey: hathi2025numberfieldmertens
authors: Shehzad Hathi; Ethan S. Lee
year: 2025
title: "Mertens' Third Theorem for Number Fields: A New Proof, Cramér's Inequality, Oscillations, and Bias"
doi: null
url: https://arxiv.org/abs/2112.02166v3
claim: The source treats Mertens products over prime-ideal norms, including the golden field; its conditional bounds and bias do not control the ordinary Robin tail, and the ideal observation does not distinguish golden unit iterates.
strata_touched: []
license: citation-only
triage: anchor
---

# Golden-field Mertens response and the retained arithmetic source

The inspected primary is
[arXiv:2112.02166v3](https://arxiv.org/pdf/2112.02166v3), revised
6 January 2025, 23 pages, with PDF SHA-256
`9342c98d92478a90f0f7128d8ee5915928ca257e3f9d3186ec3a0a42d0d95d7a`.
Theorems 1 and 3 on p.3, Theorem 5 on p.4, Theorem 22 and
Propositions 23–24 on p.17, and equation (31) with its application
in §5.4 on pp.18–20 were inspected. This note cites that version;
it does not certify the complete proof or a publisher version, rerun
its numerical density calculation, or claim Lean verification.

## The source's measure and assumptions

For a number field $K$, the source uses the prime-ideal product

$$
\mathcal P_K(x)=\prod_{N\mathfrak p\le x}
\left(1-\frac1{N\mathfrak p}\right)^{-1},
$$

whose Mertens main term is $e^\gamma\kappa_K\log x$.
Here $\kappa_K$ is the residue of $\zeta_K$ at one, and each prime ideal
is counted once. This is distinct from the rational-prime product and
from the divisor response $\sigma(N)/N$ at a fixed integer $N$.

The statements have separate hypothesis scopes:

| Source statement | Retained hypotheses and conclusion |
|---|---|
| Theorem 1 | A nonreal zero $\sigma_K$ with $1/2\le\Re\sigma_K<1$ exists and no zero has larger real part; the normalized product error has arbitrarily large positive and negative values. |
| Theorem 5 | GRH for $\zeta_K$; $\int_x^{2x}(\psi_K(t)-t)^2dt\ll_K x^2$. |
| Theorems 3 and 22 | GRH; positive lower logarithmic densities on both sides of the Mertens race, and a limiting distribution of the normalized logarithmic error. |
| Propositions 23–25 and §5.4 | GRH and generalized linear independence of positive zero ordinates; distributional formulas and bias, including a numerical calculation for $K=\mathbb Q(\sqrt5)$. |

Theorem 1 requires an attained rightmost nonreal zero. Merely excluding
a real exceptional zero does not supply that existence condition.
Its oscillation conclusion is also not a one-sided bound at every
required source. The mean-square and density statements retain their
GRH premises and their interval or logarithmic-measure conclusions;
neither supplies a bound at a specified Robin-critical cutoff.

## The actual golden-field factor is already classical

The [project's golden-ring interface](../../Blueprint/D5/S3/Arith/Lattices/GoldenIntegerRing.md)
identifies the coordinate ring $\mathbb Z[\theta]$, $\theta^2=\theta+1$,
with the ring of integers of $K=\mathbb Q(\sqrt5)$.
Equation (31), p.18, directly supplies the classical factorization

$$
\zeta_K(s)=\zeta(s)L(s,\chi_5),\qquad
\chi_5(n)=
\begin{cases}
0,&5\mid n,\\
1,&n\equiv1,4\pmod5,\\
-1,&n\equiv2,3\pmod5.
\end{cases}
$$

It therefore contains the rational zeta response and an additional
Dirichlet response. A use of the source's GRH premise for this field
already assumes RH for the rational zeta factor. The recurrence and
the two real embeddings do not supply that premise.

The [existing golden prime classification](../../Blueprint/D5/S3/PrimeForms/GoldenPrimeClassification.md)
organizes rational primes by these split, inert and ramified classes.
The local prime-ideal norms are $p,p$ for a split prime, $p^2$ for an
inert prime, and $5$ for the ramified prime. In particular a norm cutoff
$x$ includes inert rational primes only through $\sqrt x$.

To preserve this cutoff in a comparison, put

$$
\mathcal P_{\mathbb Q}(x)=\prod_{p\le x}(1-p^{-1})^{-1},\qquad
\mathcal L_5(x)=\prod_{p\le x}(1-\chi_5(p)/p)^{-1}.
$$

Reindexing the same finite Euler factors gives, for $x\ge2$,

$$
\mathcal P_K(x)=\mathcal P_{\mathbb Q}(x)\mathcal L_5(x)
\prod_{\substack{\sqrt x<p\le x\\\chi_5(p)=-1}}(1-p^{-2}).
$$

This is finite bookkeeping using the classical factorization and
splitting data, not a new Mertens theorem. The inert correction and
the signed $\mathcal L_5$ term must both be retained. Neither the
field product nor its bias is an upper bound for the original signed
Robin integral by itself. The current
[same-source requirement](polak2026finiterobinca.md) still concerns
$A=\log N$ and $I_\psi(A)>-D^*(A)$ at the actual selected integer.
An ideal-norm threshold or a logarithmic density does not identify
that integer or pay this inequality.

## The ideal observation loses the golden recurrence

In the existing FIB composition model, $M$ is multiplication by the
unit $\theta$, $J$ is golden conjugation and $C=MJ$.
For every integral ideal $I$ the induced images are therefore

$$
M(I)=\theta I=I,\qquad J(I)=\overline I,
\qquad C(I)=\theta\overline I=\overline I.
$$

Thus the four-step element rotation has only the conjugation action
after passage to ideals; its square acts as the identity there.
The same ideal represents all principal elements $\theta^j z$.
The source's ideal norm cannot recover the FIB window depth or the
quantity observer $q(a,b)=2a+3b$ from that ideal alone.

The existing translation by $\alpha=1$ gives a concrete fiber test.
The elements $1$ and $\theta$ generate the same unit ideal, but

$$
(1+1)=(2)\ne\mathcal O_K,
\qquad (\theta+1)=(\theta^2)=\mathcal O_K.
$$

Consequently this element translation does not descend to an operation
on principal ideals. These are applications of the existing unit and
ideal relations, not a new no-go theorem or an obstruction to retaining
the elements and their observers. A representation for the full affine
FIB behavior must retain more than the ideal response.

The field supplies a genuine classical prime splitting slice and an
independent $L(s,\chi_5)$ response. Its known conditional estimates,
unit quotient and finite-cutoff accounting specify what a bridge back
to Robin would have to retain; they provide no new signed estimate,
critical-source coverage or proof of RH. All applications in this note
are at paper level, without new Lean declarations or an originality claim.
