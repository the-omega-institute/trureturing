---
bibkey: graffeogubbiotti2024cremona
authors: Michele Graffeo, Giorgio Gubbiotti
year: 2024
title: "Growth and Integrability of Some Birational Maps in Dimension Three"
doi: 10.1007/s00023-023-01339-5
url: https://arxiv.org/abs/2301.09129v2
claim: "The KHK discretisation of the Euler top decomposes as l2 o crem3 o l1 with two projectivities and the standard cubic Cremona map of P^3 (Lemma 2.6); Remark 7.7 conjectures that the KHK map of a quadratic three-dimensional Nambu system with positive definite Nambu-Hamiltonians is, up to conjugation by a projectivity, of the same type (A)-(i)."
strata_touched:
  - D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition
license: citation-only
triage: anchor
---

# Graffeo–Gubbiotti, growth and integrability of birational maps in dimension three

## Verified locator

DOI: 10.1007/s00023-023-01339-5

Source: https://arxiv.org/abs/2301.09129v2

Ann. Henri Poincaré 25 (2024), 1733–1793.

M. Graffeo and G. Gubbiotti, arXiv:2301.09129v2 [math.AG] (3 June 2023, the latest version); Ann. Henri Poincaré 25 (2024), 1733–1793. Quotations are from the v2 TeX source `GG_cremona_v1_clean.tex`.

The KHK discretisation (Definition `def:khk`):

> $\frac{\vec{x'}-\vec{x}}{h} = 2\vec{f}\left( \frac{\vec{x'}+\vec{x}}{2} \right)-\frac{\vec{f}\left( \vec{x'} \right)+\vec{f}\left( \vec{x}\right)}{2}$

The Euler-top decomposition (Lemma `lem:eulerdecomposition`):

> The KHK discretisation of the Euler top decomposes as $\Phi_{h} = \ell_{2}\circ \mathrm{crem}_{3} \circ \ell_{1}$ where $\ell_{i}\colon \mathbb P^{3}\to\mathbb P^{3}$ are two projectivies

The Nambu systems and the conjecture (Remark `ex:celledoni`):

> $\dot{\vec x} = \nabla H_{1}(\vec{x}) \times \nabla H_{2} (\vec{x})$, where, for $i=1,2$, $H_{i}(\vec{x})=\vec{x}^{T} A_{i} \vec{x}$ is a Nambu–Hamiltonian function. […] We conjecture that, up to conjugation by a projectivity, the map $\Phi_{h}^{(N)}$ is of type (A)-(i), i.e. it exists an analogue of Lemma 2.6 for the map $\Phi_{h}^{(N)}$.

The same remark records that the invariant net "is generic in the sense that its base locus consists of eight distinct points" and that "The matrices $A_1$ and $A_2$ are positive definite symmetric quadratic forms."

## Encoding and boundary

For a quadratic homogeneous vector field the KHK step is $x'-x=h\,\bar f(x,x')$ with the symmetric polarisation $\bar f$; for $f=4\,Ax\times Bx$ this is $x'=(I-2hL_x)^{-1}x$ with $L_xv=Ax\times Bv+Av\times Bx$, and its homogeneous lift is $(\operatorname{adj}M\,x,\det M)$ with $M=x_4I-2hL_x$. The repository proves the decomposition $\Phi^{(N)}_h=\ell_2\circ\mathrm{crem}_3\circ\ell_1$ as an equality of homogeneous lifts for every positive definite pair whose generalised eigenvalues are distinct and every $h>0$; the source's eight-point genericity implies that eigenvalue condition. Degenerate pencils, the converse of the genericity implication and the source's growth classification are outside this conclusion.
