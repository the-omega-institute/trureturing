---
bibkey: barrykevrekidis2013vortex
authors: Anna M. Barry, Panayotis G. Kevrekidis
year: 2013
title: "Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability"
doi: 10.1088/1751-8113/46/44/445001
url: https://arxiv.org/abs/1306.1545v2
claim: "The paper studies equilibria and linear stability of few-vortex clusters in the precessing point-vortex model of a Bose–Einstein condensate and conjectures (Conjecture 4.4) that for N >= 6 the regular N-gon of alternating charges has N/2 - 2 distinct pairs of real eigenvalues."
strata_touched:
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonCartesianChain
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonJordan
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonNeutral
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonOrientation
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalDerivative
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonPhysicalSpectrum
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealBoundary
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonSmallCases
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport
  - D5/S3/FluidDynamics/Vortices/InverseChordCirculant
license: citation-only
triage: anchor
---

# Barry–Kevrekidis, few-particle vortex cluster equilibria

## Verified locator

DOI: 10.1088/1751-8113/46/44/445001

Source: https://arxiv.org/abs/1306.1545v2

J. Phys. A: Math. Theor. 46 (2013), no. 44, 445001, published 18 October 2013.

A. M. Barry and P. G. Kevrekidis, arXiv:1306.1545v2 [nlin.PS] (10 June 2013, the latest version).

## Statement

The model is the precessing point-vortex system (Section 2, Eqs. (1)–(2), with $b=2$)
$$\dot x_j=-S_j\Omega y_j-\frac b2\sum_{k\ne j}S_k\frac{y_j-y_k}{|\mathbf x_j-\mathbf x_k|^2},\qquad \dot y_j=S_j\Omega x_j+\frac b2\sum_{k\ne j}S_k\frac{x_j-x_k}{|\mathbf x_j-\mathbf x_k|^2}.$$
Section 4.1 takes alternating charges $S_j=(-1)^{j+1}$ at $z_j=e^{2\pi ij/N}$; Lemma 4.2 gives the equilibrium with $\Omega=1/2$ for even $N$. The paper states:

> **Conjecture 4.4.** For $N\geq 6$, the $N$-gon has $\frac{N}{2}-2$ distinct pairs of real eigenvalues.

## Encoding and boundary

The repository defines the vector field of Eqs. (1)–(2) with $b=2$ and $\Omega=1/2$, the regular unit $N$-gon and the Jacobian matrix of partial derivatives at it. It proves that for $N=2m$, $m\ge3$, the nonzero real eigenvalues are exactly $\pm\frac{(m-k)\sqrt{k^2-2}}2$, $2\le k\le m-1$, and that these $m-2$ values are distinct. The Gross–Pitaevskii PDE stability, odd $N$, other charge patterns, eigenvectors and Krein signatures are outside this conclusion.

## Full-spectrum source and Cartesian correspondence

Haobo Ma and Wenlin Zhang, in that order, *Extending Barry–Kevrekidis (2013): the polygon spectrum in Section 4.1, Conjecture 4.4, p. 12*, released note revision 2, 4 November 2026, gives the complete polynomial, complex multiplicities, neutral Jordan chain, positive-parameter scaling and odd/even boundary. Its finite and numerical checking files have only their stated finite ranges and tolerances. They do not establish the universal results. The already formalized Conjecture 4.4 count and its separation, actual field, derivative, rotation, inverse-chord, Fourier and determinant proofs are canonical suppliers. These are reused, with no new-discovery or priority claim. Barry–Kevrekidis retain prior equilibrium, instability and small-spectrum credit.

The note uses zero-based angles $2\pi j/N$, whereas the canonical formal polygon has angles $2\pi(j+1)/N$. A common rotation relates them; the formal charge $(-1)^{j+2}$ equals $(-1)^j$. The canonical product supplier uses $CB$, whereas the note writes $BC$; their characteristic determinants correspond, and the full paired coordinate proof specifies the actual restrictions.

Two primary-source discrepancies remain explicit. In arXiv:1306.1545v2, `BEC_VFP6.tex` lines 314–317 (Eq. (12), also PDF page 5) states unit radius, $b=2$, $\Omega=1/2$ but prints square roots $\pm i/\sqrt2$ and twice $\pm i/4$. Differentiating the declared Cartesian field gives instead $\pm i\sqrt2$ and twice $\pm i/2$, and the square polynomial $\lambda^2(\lambda^2+2)(\lambda^2+1/4)^2$. We do not infer a typo or normalization explanation, nor claim literal numerical agreement with the printed Eq. (12).

Also, the complex Eq. (4), TeX lines 201–203, has an interaction sign differing from Cartesian Eqs. (1)–(2), lines 170–174. Multiplying those Cartesian equations by $i$ gives a minus sign before the reciprocal-conjugate interaction in $i\dot z$. The formal actual-field results use the explicit Cartesian equations. No equivalence to the inconsistent printed complex equation, journal/erratum resolution, upstream edit or release change is asserted.

The extensions concern the constant-precession point-vortex field on collision-free configurations, with positive $b,\Omega$ and radius $\sqrt{b/(4\Omega)}$. They assert no nonlinear or PDE stability, nonconstant-precession, unequal-ring, central-vortex, all-equilibria or collinear-stability result. Spectral neutrality in the dipole and square is compatible with an unbounded neutral linear drift orbit.
