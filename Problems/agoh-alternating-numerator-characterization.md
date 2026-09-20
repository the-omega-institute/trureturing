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
Its frozen public theorem
`D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.result` has type
`Not fullClaim` and statement identity
`sha256:2a75da54a52fd95296805f384b83c5fe22e153eff87d5ed70694a9ce4125d3fb`.
The number 413 encodes the three base-nine digits [8,0,5], from least to most
significant. Subtracting four gives the actual coefficients [4,-4,1], which
reconstruct 4-4X+X^2=(X-2)^2. This polynomial is nonzero, splitting and
nonconstant, has value one at X=1, satisfies the actual reduced-numerator
divisibility for every natural order, is not a monomial, and has a repeated
root at 2. The universal property includes n=0 and uses the reduced
`RatFunc.num` of the literal Equation (3.1) rational sum. It therefore refutes
the full conjectured equivalence under the printed and contextual source
hypotheses, not a finite-order or common-numerator surrogate.

## Triage

`theorem`, targeting a published named conjecture under the
open-problem-resolution basis. Universal symbolic algebra is the mathematical
content; the coefficient code is its actual witness, not a bounded
enumeration offered as a substitute. The frozen `result` theorem carries the
single typed `OpenProblemResolutionClaim` with `ResolutionKind.Refuted` for
this dossier. Repository merge and solved-problem KPI credit are not asserted.

## ASSUMED-UNVERIFIED

The bounded audit covered the journal volume, official Zenodo record,
DataCite, and exact-title, author, and topic arXiv searches. Crossref did not
index the Zenodo DOI and its title results were noisy; OpenAlex was
rate-limited, and Semantic Scholar yielded no usable DOI record. Worldwide
absence of a prior resolution is not proved, and no publication-priority
claim is made. Preregistration #8702 credits the complete target, and project
handoff #7333 comment 5733245266 credits the released counterexample route.
