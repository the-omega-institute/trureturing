---
bibkey: alpoge2026riemann
authors: Levent Alpöge
year: 2026
title: Riemann hypothesis formalization in Lean
doi: null
url: https://github.com/the-omega-institute/riemann-hypothesis
claim: Numerical Landau comparisons, the long power-window zero-exclusion route, and the common integral lattice frame slope bound.
strata_touched:
  - D5/S3/Analytic/Laplace/LongWindowBounds
  - D5/S3/Analytic/Laplace/LongWindowPoleExclusion
  - D5/S3/CharacterSums/DirichletCyclicWindowZeroFree
  - D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation
  - D5/S3/Combinatorics/Lattices/EuclideanCommonLattice
  - D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism
license: citation-only
triage: anchor
---

# Riemann hypothesis formalization in Lean

## Verified locator

- URL: https://github.com/the-omega-institute/riemann-hypothesis
- Revision: `c7d25b3bfd7906388bb8eb0774e027a2b756a7b6`
- Directory: `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`
- Frame slope statement: `src/Formalism/HarderNarasimhan/StatementFrameF.lean`, `Formalism.HN.TheoremFSharp`; proof `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean`, `Formalism.HN.frame_theorem_sharp`

## Source declarations

- `LandauGrowthContra.lean`, `Deduction.landau_growth_contra`: for positive c,d
  and d<e, there are positive eta and a cutoff U0 such that for all U>=U0 and
  natural k>=U, C exp(eta U)/e^k < c/d^k. Its proof chooses
  eta=log(e/d)/2 and U0=2|C|/(c log(e/d)).
- `landauWindow.lean`, `Deduction.landau_window_contra`: for positive c,d and
  d<e<=E, the two-error coefficient bound cannot recur at arbitrarily late U
  for every positive exponential loss eta.
- `landauWindow.lean`, `Deduction.landau_window`: the pole geometry, Cauchy
  coefficients and long-window moment estimates exclude poles on the right.
- `ZeroFreeOfRpowWindow.lean`, `Deduction.zeroFree_of_rpow_window`: the long
  power-window upper-bound hypothesis yields zero exclusion.

The numerical arguments above are literature-attested. The local declarations
retain that core and expose additional results: the growth theorem states the
chosen eta and nonnegative U0 explicitly; the window contradiction allows d<E
independently of d<e, using min(e,E). These strengthenings are repo-derived.

The local pole theorem allows theta>=0 and poles with real part at most one.
It exposes a fixed sigma>2, theta<sigma, E=sigma-theta, strict d<e<E,
nonnegative B,K, and the common order floor(sigma*((2+delta)/2)*U).
The actual cyclic-family application constructs its own arithmetic transform
and positive residues. Its final criterion allows every real theta. For
nonpositive theta the window premise is impossible, by the existing genuine
nontrivial zeta zero and a positive-exponent lift. This is not an extension of
the analytic continuation domain. These parts are repo-derived, not claims
that the pinned source states the strengthened local declarations verbatim.

## Common integral lattice frame slope estimate

The source treats Hermitian lattices over a totally complex number field.
Integral maps into one common target lattice, an average source slope lower bound,
a maximal source slope bound, and two near-orthogonality moments yield the
following inequality. In the source statement the total source dimension is
positive, every frame weight is strictly positive, and the parameters satisfy
0 <= u, 0 <= H, 0 <= eta, 0 <= e <= 1/4 and 0 <= delta < 1.
Writing D for the padded target dimension and d for the unpadded target
dimension, the source also requires (1-delta)D <= d. Its padded frame maps
have the prescribed unpadded coordinate rows of the arithmetic maps.

\[
s-\mu(C)\le
\frac{4u\log(1+H/u)+(\eta+4\sqrt e)H}{1-\delta}.
\]

The repository's real integer-lattice theorem allows arbitrary real frame
weights and e < 1. It derives nonnegativity of u, e and eta from its data,
requires H >= 0 and d > 0, and gives the exact ratio D/d times the same
numerator. It also retains the weighted bound
m(s-mu(C)) + (d-m)H <= D times that numerator, where m is the integral rank
of C. The delta form follows under delta < 1 and (1-delta)D <= d;
nonnegativity of delta is not needed in the repository version.
These are repository-derived extensions, not the original source's parameter
range or a direct number-field specialization.

The logarithmic term is zero when (u=0). The coefficients four are preserved
by the following affine change within a fixed category of objects and subobjects:

\[
\mu_{\rm src}=2\mu_0+c_K,\quad h_{\rm src}=2h_0,\quad
s_{\rm src}=2s_0+c_K,\quad u_{\rm src}=2u_0,\quad H_{\rm src}=2H_0.
\]

Subtracting the common slope constant and dividing the inequality by two gives
the same coefficients in the variables with subscript zero. For the same real
covolume, the source's average slope equals twice minus the logarithm of that
covolume divided by underlying integral rank, plus its field normalization.
This average-degree identity alone does not identify Harder-Narasimhan spectra.
Saturated subobjects over the ring of integers and all saturated integer
sublattices of the underlying real lattice are different subobject classes.
Their maximal and minimal slopes cannot be identified by this normalization alone.

Writing r2 for the number of complex places, the source height is

\[
h_{\rm src}(B)=\frac1{r_2}\sum_v\log\lVert B_v\rVert_{\rm op}^2
=\frac2{r_2}\sum_v\log\lVert B_v\rVert_{\rm op}.
\]

The induced map on the real orthogonal direct sum instead has logarithmic
operator norm equal to the maximum of the logarithmic norms at those places.
The factor two compares squared and unsquared logarithmic norms with the same
averaging convention; it does not replace that average by a maximum.
Realification of a complex frame doubles dimensions, traces and squared
Hilbert-Schmidt norms, leaving its normalized parameters e and eta unchanged.
These correspondences explain the matching coefficients, rather than asserting
that the real integer-lattice theorem is a direct number-field specialization.

### Scope

The real integer-lattice argument requires its own integral morphism comparison
and compatibility between HN sublattices and the real frame maps. A finite
spectral frame estimate does not by itself establish either arithmetic bridge.
This note attributes the common-lattice method and the stated source theorem;
the real-lattice bridge proofs are repository derivations.
