---
bibkey: connesconsani2020quasiinner
authors: Alain Connes and Caterina Consani
year: 2020
title: Quasi-inner functions and local factors
doi: null
url: https://arxiv.org/abs/2008.10974v1
claim: Products of local-factor ratios containing the archimedean place have compact off-diagonal Hardy blocks, and their Sonin kernels form an injective inductive system. This supplies neither a signed trace comparison nor an unsmoothed trace-class estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Quasi-inner local products and Sonin transport

The inspected primary manuscript is [arXiv:2008.10974v1](https://arxiv.org/pdf/2008.10974v1), 25 August 2020, 25 pages, SHA-256 `c2f116d90e93600909449cb89983e02feea2ed950bf4ad6d91cb6c7cac7e1141`. All locators below refer to this version; no publisher-edition identity is asserted. These are reused source results, without a new proof, numerical reproduction or Lean declaration. Selected statement and argument inspection is not a complete proof audit.

## Quantitative compactness of the actual local product

For a half-plane or disk $\Omega$, the source calls a unimodular boundary function $u$ quasi-inner when $(I-P)uP$ is compact, with $P$ the orthogonal projection onto $H^2(\Omega)$ and $u$ acting by multiplication. This $P$ is a **Hardy projection**, distinct from the orthogonal projection onto physical Sonin vectors.

Write $\rho_v(z)=\gamma_v(z)/\gamma_v(1-z)$ for the local-factor ratio. Theorem 4.8, manuscript p.22, treats $m\ge1$ finite primes together with the archimedean place. It states that

$$
u_F(z)=\rho_\infty(z)\prod_{p\in F\setminus\{\infty\}}\rho_p(z)
$$

is quasi-inner relative to $\operatorname{Re}z<1/2$, and that its off-diagonal block $(I-P)u_FP$ is an infinitesimal of order $1/(2m)$. Fact 3.6 records that an individual finite-place ratio is not quasi-inner. The full product and the individual factors therefore have different operator contracts.

The stated singular-value order is a compactness estimate. It does not by itself give a trace-class bound for that unsmoothed block, nor the sign of a dilation-smoothed trace correction. No positive ordering is part of Theorem 4.8.

## Sonin kernels and the actual transport maps

Definition 5.2, manuscript p.23, defines the abstract Sonin space

$$
\mathcal S(u)=\ker\bigl((I-P)u(I-P)\bigr)
$$

on the complementary Hardy space. Theorem 5.3 on the same page proves that these kernels are infinite-dimensional for finite place sets containing $\infty$. For $F\subsetneq F'$, it gives an injective map

$$
\mathcal S(u_F)\longrightarrow\mathcal S(u_{F'}),
\qquad
\xi\longmapsto
\left(\prod_{p\in F'\setminus F}(1-p^{-z})\right)\xi.
$$

This is an injective inductive system; the source does not assert that these multiplication maps are unitary or preserve the needed orthogonal trace.

Proposition 5.5, manuscript p.24, identifies the physical archimedean Sonin space $\mathcal S(1,1)$ with $\mathcal S(\rho_\infty)$ under the source unitary half-density and Mellin maps, equations (24)–(25). This supplies a physical-to-Hardy interface at the archimedean place. The [later semilocal source](connesconsanimoscovici2024semilocal.md) supplies the physical $\theta_S$ isomorphism and explicitly different entire-function inner products.

## What the compactness result does not settle

The [physical projection supplier](burnol2002sonine.md) gives an explicit unweighted Sonin resolvent. These Hardy-block and transport results add genuine operator structure, but neither source estimates the orthogonal projection correction in the Euler-factor metric on a fixed common integrating test.

The [archimedean signed comparison](connesconsani2021archimedean.md) remains support-restricted; [local time delay](burnol1999scattering.md) retains the arithmetic sign and correction. Combining separate compactness, positivity and transport statements does not supply the missing full same-test signed comparison. No such comparison or RH proof is claimed here.
