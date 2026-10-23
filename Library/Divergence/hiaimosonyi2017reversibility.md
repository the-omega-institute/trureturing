---
bibkey: hiaimosonyi2017reversibility
authors: Fumio Hiai and Milan Mosonyi
year: 2017
title: Different quantum f-divergences and the reversibility of quantum operations
doi: null
url: https://arxiv.org/abs/1604.03089v4
claim: Standard quantum f-divergence preservation detects reversibility when the support of the representing measure covers the distinct spectral sites of the two relative modular operators.
strata_touched:
  - D5/S3/Quantum/Divergence/ResolventFunctionalRigidity
license: "not verified; bibliographic attribution only, with no source text or proof code copied"
triage: anchor
---

# Spectral support and reversibility

## Verified locator

https://arxiv.org/abs/1604.03089v4

The source is arXiv:1604.03089v4, dated 27 June 2017, Theorem 3.18,
printed pages 18–20. In item (iv), condition (3.21) compares the cardinality
of the support of the operator-convex representing measure with the union
of the spectra of the input and output relative modular operators. The
source assumes support containment and a 2-positive trace-preserving map;
it does not claim that strict scalar convexity alone is sufficient.

The source's standard divergence uses the relative modular direction
L_rho R_sigma^{-1}. The project's existing logarithm-to-Petz coordinates
use L_sigma R_rho^{ominus} on the supported spectral carrier. Transferring
a general f-divergence between these directions requires its scalar
transpose and actual support boundary terms. This library note does not
assert that transfer has been established.

## Finite spectral identification used by the project

For finitely many distinct nonnegative sites s and complex residues c_z,
consider R(t) = sum_{z in s} c_z/(z+t). Multiplication by the common
denominator gives the polynomial

P(t) = sum_{z in s} c_z product_{w in s, w != z}(t+w).

Its degree is at most |s|-1. Thus |s| distinct positive zeros of R force
P=0. Evaluating at -z leaves c_z product_{w != z}(w-z), whose second
factor is nonzero. Every residue therefore vanishes. An empty site set
is immediate. Grouping repeated eigenvalues reduces finite spectral
readouts to this argument and includes a possible zero eigenvalue.

`ResolventFunctionalRigidity` uses the existing contraction-defect identity
to turn vanishing actual quadratic defects into resolvent-vector equalities,
then applies this polynomial argument to the union of the two spectra.
It concludes intertwining for every real spectral function without a
continuity hypothesis. The all-positive-shift result consumes the finite
sampling theorem; the original logarithm-to-fixed-Petz chain is retained.
The polynomial root bound is reused from the pinned Mathlib library.

This is a formalization of known finite rational spectral rigidity motivated
by the source's support criterion, with no claim of mathematical originality.
No proof code or prose from the article is copied. The theorem alone proves
neither the Loewner representation nor the full standard f-divergence
preservation/recovery equivalence: the representing measure, support-to-zero
implication and singular boundary terms remain separate obligations.
