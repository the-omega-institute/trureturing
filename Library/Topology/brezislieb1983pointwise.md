---
bibkey: brezislieb1983pointwise
authors: Haïm Brézis and Elliott H. Lieb
year: 1983
title: A relation between pointwise convergence of functions and convergence of functionals
doi: 10.1090/S0002-9939-1983-0699419-3
url: https://sites.math.rutgers.edu/~brezis/PUBlications/99-journal.pdf
claim: Theorem 2, its strong L1 remark and power Example (a) imply full absolute L1 power splitting for complex functions on an arbitrary measure space for every positive real exponent; Theorem 1 states the corresponding signed energy splitting.
strata_touched:
  - D5/S3/Topology/Measures
license: citation-only
triage: anchor
---

# Positive-power splitting

## Verified locator

Haïm Brézis and Elliott H. Lieb, Proceedings of the American Mathematical
Society **88** (1983), no. 3, 486–490.
DOI: https://doi.org/10.1090/S0002-9939-1983-0699419-3.
The complete primary text is available at
https://sites.math.rutgers.edu/~brezis/PUBlications/99-journal.pdf.
Theorem 1 and Theorem 2 are on printed page 487; the strong L1 remark,
proof of Theorem 2 and power Example (a) are on printed page 488.
The introductory measure space and complex scalar convention are on
printed page 486. The PDF includes a cover page before printed page 486.

## Statement and source correspondence

Let mu be an arbitrary measure on a measurable space Omega, let p > 0,
and let f(n) be complex functions which are almost-everywhere strongly
measurable, converge almost everywhere to g, and satisfy a common finite
bound M on the nonnegative integral of norm(f(n))^p. The limit is
almost-everywhere strongly measurable and has the same mass bound.
The limit power, every original power, every residual power and every
real defect are integrable. With

    r(n)(x) = f(n)(x) - g(x),
    d(n)(x) = norm(f(n)(x))^p - norm(r(n)(x))^p - norm(g(x))^p,

the integral of abs(d(n)) tends to zero. Consequently the difference
between the integrals of the original and residual powers tends to the
integral of the limit power. The latter conclusion is signed splitting;
the absolute-defect conclusion is stronger.

Theorem 2 treats continuous j on the complex scalars with j(0) = 0 and
an epsilon increment estimate. Its formula (4) and Remark (ii) give strong
L1 convergence. Example (a) takes j(z) = abs(z)^p for all 0 < p < infinity.
Fatou's lemma gives integrability of the limit power; the elementary Lp
sum/difference inequalities transfer the original uniform power bound to
the residual sequence. These give the hypotheses of the power example.
The explicit integrability conjuncts also justify each real Bochner
integral in the signed conclusion. The arbitrary-measure scope needs no
finite or sigma-finite measure hypothesis. A common integrable dominator,
uniform integrability, tightness, weak convergence, a subsequence and
convergence of the separate energies are not premises of this result.

The declaration
`D5.S3.Topology.Measures.BrezisLiebPowerDefect.brezis_lieb_power_defect`
states precisely this positive-power conclusion, with a finite bound
M of type NNReal, extended nonnegative integrals for mass bounds and
real Bochner integrals for energies. Its scalar range is complex.
It states no general nonlinear j theorem and no vector-valued extension.
The increment estimate and truncation argument are classical mathematics;
no mathematical originality or resolution of an external open problem
is asserted.

## Moving mass

On the natural numbers with counting measure, put g(0) = i and g(k) = 0
for k > 0. Let f(n) equal i at 0 and n+1, and zero elsewhere. Then f(n)
converges pointwise to g. For every positive p, the original power mass
is two, the limit power mass is one, and the residual power mass is one.
Their supports are disjoint, so d(n) is identically zero. The residual
does not converge strongly to zero in power mass. Any common power
dominator must be at least one at every natural number, hence cannot be
integrable for counting measure.

## Contemporary application boundary

The primary article at https://arxiv.org/html/2611.26428v1 uses the
Brézis–Lieb lemma immediately after formula (2.25) to split the nonlinear
mass of a convergent minimizing sequence into limit and residual masses.
The displayed relation is sigma^(p+1) + tau^(p+1) = 1. Its use with (2.25)
also needs the separate quadratic kinetic estimate and the nonvanishing
condition cited there as (2.20). Nonlinear power splitting alone proves
neither a kinetic decomposition nor nonvanishing, compactness, existence
of a minimizer or a PDE solution.
