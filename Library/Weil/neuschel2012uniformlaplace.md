---
bibkey: neuschel2012uniformlaplace
authors: T. Neuschel
year: 2012
title: A uniform version of Laplace’s method for contour integrals
doi: 10.1524/anly.2012.1147
url: https://doi.org/10.1524/anly.2012.1147
claim: Theorem 3.1 supplies uniform local contour asymptotics on a compact parameter set; its fixed-contour and uniform-gap hypotheses must be verified after the original bump’s outer rescaling.
strata_touched: []
license: citation-only
triage: anchor
---

# Uniform local asymptotics and the finite outer interface

The published article is *Analysis* **32** (2012), 121–135. Its [institutional full text](https://lirias.kuleuven.be/retrieve/d8d1b738-7dc3-4484-9956-41058d57b9d9) contains Theorem 3.1 on printed pp.125–126. The defining hypotheses and conclusion below are literature-attested. The PDF is copyrighted; this note retains bibliographic information and the application conditions, without redistributing its text or file.

The theorem concerns

$$
I(n,z)=\int_P e^{-np(t,z)}q(t,z)\,dt,
$$

where the contour $P$ is fixed and the auxiliary complex parameter $z$ lies in a nonempty compact set. The phase and amplitude are jointly continuous and holomorphic in the contour variable. At the finite starting point they have convergent local expansions of positive integer orders with nonzero leading coefficients. The real phase difference is uniformly positive at every later contour point and has a positive lower bound near the final endpoint. A common absolute-integrability bound at some fixed integer $N$ is also required. The conclusion is a complete uniform asymptotic expansion, with the branches specified by the initial contour direction and the leading phase coefficient.

The large parameter $n$ is a positive integer, as stated in the introduction and theorem. An application to every large real or complex parameter cannot silently discard this restriction.

## Parameter mapping for the existing outer kernel

The [original-test outer interface](../../docs/develop/theory/RH_RESEARCH_LANE_THEORY.md), §35, retains $x=iT(1-i\tau)$, $|\tau|\le1/(2H)$, and all five complex leading contributions. In its endpoint rescalings the local kernel is

$$
e^{-\mu(v+v^{-1})},\qquad \Re\mu>0,
$$

with $|\mu|\asymp T^{1/2}$ at a same-endpoint contribution and $|\mu|\asymp T^{1/4}$ at the cross contribution. The rescaled parameters lie in a fixed closed sector strictly inside the right half-plane.

To apply the source theorem locally, choose a fixed $h\in(0,1)$ and split the neighborhood of the stationary point into $v=1+t$ and $v=1-t$, $0\le t\le h$. Put

$$
n=\lfloor|\mu|\rfloor,\qquad z=\mu/n.
$$

For sufficiently large $|\mu|$, the auxiliary parameters lie in the compact set $1\le|z|\le2$, $|\arg z|\le\pi/3$, while $nz=\mu$ holds exactly. Thus this substitution preserves every real $T$ and $R$; it does not select a sequence of scales. The two fixed local phases are

$$
p_\pm(t,z)=z\bigl((1\pm t)+(1\pm t)^{-1}\bigr).
$$

Their uniform positive gaps are explicit:

$$
\Re\bigl(p_\pm(t,z)-p_\pm(0,z)\bigr)
=\Re z\,\frac{t^2}{1\pm t}>0\qquad(0<t\le h).
$$

The local phase order is $2$ and the amplitude order is $1$. On these fixed compact intervals, holomorphy, convergent expansions and common absolute integrability follow directly. For a fixed analytic local amplitude, the source’s two half-expansions combine; the first odd corrections cancel. This provides the uniform local saddle estimate already expressed through Bessel moments in §35.

## Obligations outside the local source theorem

The exact normalized amplitudes of the original nested integral depend on $T$. They must be compared with their fixed local models with a uniform error; they are not automatically another admissible parameter family in Theorem 3.1. At the cross saddle the local model contains $e^{av^2/4}$. Extending that model to the whole positive real axis would produce a divergent integral, so its use remains confined to a fixed neighborhood of $v=1$.

The source theorem does not itself deform the original finite outer interval, retain its connecting faces, control the entire increasing rescaled range, or transport the exact inner analytic remainder. Those are the separate kernel-specific conditions supplied by §35. The [earlier source note](tlas2020bump.md) preserves the complementary Bessel, single-endpoint and global-saddle sources and their application boundaries.

Uniform local asymptotics therefore supply a reusable existing method, not the actual zero-sum sign. Even after the finite outer interface is established, its multiplicity-weighted positive error envelope must be compared jointly with the signed leading sum and the same fixed head. This note supplies no such comparison, no all-scale Weil positivity, no RH or Robin conclusion, and no FIB-to-prime transport.
