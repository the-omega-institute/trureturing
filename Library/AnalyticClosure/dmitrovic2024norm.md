---
bibkey: dmitrovic2024norm
authors: D. Dmitrović
year: 2024
title: "Norm of composition operator on mixed norm spaces"
doi: 10.7153/oam-2024-18-42
url: https://doi.org/10.7153/oam-2024-18-42
claim: "The conjecture on page 705 asserts the constant-one point evaluation estimate for all positive mixed-norm exponents."
strata_touched:
  - D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs
  - D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result
license: citation-only
triage: anchor
---

# Mixed-norm point evaluation

## Locator

DOI: https://doi.org/10.7153/oam-2024-18-42

Article: https://files.ele-math.com/articles/oam-18-42.pdf

D. Dmitrović, *Norm of composition operator on mixed norm spaces*,
Operators and Matrices 18(3) (2024), 697–710. Definitions are on page 697;
Lemma 2 and the conjecture at the end of section 2 culminate on page 705.

## Source statement

> CONJECTURE. From the previous discussion, we conjecture that for all 0 < p, q ⩽ ∞, 0 < α < ∞ and f ∈ H^{p,q,α}: |f(z)| ⩽ ‖f‖_{p,q,α} / (1 − |z|²)^{α + 1/p}.

The finite-q norm is the q-th root of the radial integral with density
$2\alpha q r(1-r^2)^{\alpha q-1}$ and angular mean to the q-th power.
For q equal to infinity it is the supremum of the angular mean multiplied
by $(1-r^2)^\alpha$. The angular mean is the normalized p-th power
integral on the circle, or the angular supremum when p is infinity.

Lemma 2 proves constant one for finite positive p and q with p/q at least
one, and for p equal to infinity. For finite q greater than p its upper
constant is $2^{\alpha+3/p}$. For finite p and infinite q the upper
constant is $2^\alpha(1+3|z|)^{1/p}(1+|z|)^{1/p}$.

## Source boundary

The definitions and universal claim are represented by Defs. The theorem
Result.result refutes that claim. Result.fails_off_contractive_range proves
failure for every finite positive p, every q greater than p including
infinity, and every positive alpha. The principal-branch family is bounded
and holomorphic on the unit disc. Lemma 2's positive range and the exact
optimal constants outside it are not formalized by these modules.
