---
slug: agoh-alternating-numerator-characterization
bibkey: agoh2026intrinsic
doi: 10.5281/zenodo.18154119
url: https://math.colgate.edu/~integers/aa9/aa9.pdf
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/InformationEscape/TheoremUnit
---

# Agoh's alternating-numerator characterization

## Problem

The sole target is the unnumbered Conjecture on final printed page 9 of
INTEGERS 26 (2026), A9. Its exact source and provenance are in the linked
Library note. For every nonzero real polynomial f splitting over the reals,
the asserted equivalence is:
`(for every natural n, (X-1)^n divides num(Q_n(f))) iff
(f is a monomial or every real root is simple and different from 1)`.
Q_n is independently the literal rational sum in Equation (3.1), and num is
its actual reduced `RatFunc.num`. The all-n condition is inside the equivalence.

## Motivation

The printed discussion asks whether simple roots are necessary, not only
sufficient, for the all-order factor property. Indexed coefficient readouts
retain the actual counterexample polynomial through the existing theorem-unit
machinery; they do not replace its universal algebraic certificate.

## Gap

The supplied bounded literature audit found no accessible resolution in the
checked journal, Zenodo, DataCite and arXiv scope. Preregistration #8702
credits the released mathematical sketch #7333 comment 5733245266.
No exhaustive historical-openness or priority claim is made. The source's
partial-fraction treatment of repeated roots does not establish necessity.

## Route

Use f=(X-2)^2. Set t_i=f(X^i), D=product_i t_i and
N=sum_i (-1)^i binom(n,i) product_{j != i} t_j, indexed over 0 through n.
The indexed deletion identity expresses each deleted product using powers
of t_i and coefficients of product_j(Y+t_j), equivalently the elementary
symmetric polynomials of Equation (2.3). Expanding f^k by coefficients gives
sum_i (-1)^i binom(n,i) f(X^i)^k =
sum_r coeff(f^k,r)(1-X^r)^n. Thus (X-1)^n divides N for every n, including 0.

For this f, D(1)=1, every denominator polynomial is nonzero and the literal
Q equals N/D in RatFunc Real. The reduced-fraction identity gives
num(Q)*D=N*denom(Q). The remainder theorem gives an explicit Bezout identity
for X-1 and D; coprimality of their powers cancels D in the divisibility
argument. The coefficients 4 and -4 exclude monomials, while root 2 has
multiplicity 2. The certificate also proves f nonconstant and f(1)=1.

## Falsifier

A failure of the actual Q=N/D bridge, of denominator nonvanishing, of
coprime cancellation, or of either excluded alternative invalidates this
route. A finite collection of n tests would not establish the target.

## Evidence

The source-specific Lean module is
`D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.lean`.
Its only public mathematical theorem is
`result : (let counterexample := actualWord; Not fullClaim)`, definitionally
the full closed negation. The actual word has codes [8,0,5], decoded by
subtracting 4 to coefficients [4,-4,1]. Its law contains the full
CounterexampleCertificate, not a sampled or truth-valued placeholder.
The three CUT slots are coefficient readings. Changing any one code changes
the law. The legacy bridge derives the full refutation from the certificate.
Continuation is explicitly open, with no residual certificate claimed.

## Triage

`theorem`, targeting a published named conjecture under the
open-problem-resolution basis. Universal symbolic algebra is the mathematical
content; the coefficient word is its actual witness, not a bounded
enumeration offered as a substitute. Independent review and caller-owned
freeze-last delivery remain required before solved-problem credit.

## ASSUMED-UNVERIFIED

The supplied earlier external searches were not rerun in this implementation
call. Crossref was noisy/DOI404, OpenAlex429 and Semantic Scholar unavailable
remain explicit source-audit limits. Worldwide absence of a prior resolution
is not proved. Current implementation review, freeze, remote CI and merge
are not asserted here. After review and canonical freezing, add the Scribe
OpenProblemResolutionClaim(Refuted); its current host must be frozen, so no
prefreeze pin or resolution marker is fabricated.
