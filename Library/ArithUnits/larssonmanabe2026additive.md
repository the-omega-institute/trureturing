---
bibkey: larssonmanabe2026additive
authors: Urban Larsson and Hikaru Manabe
year: 2026
title: Additive Subtraction Games
doi: 10.48550/arXiv.2603.10414
url: https://arxiv.org/html/2603.10414v2#Thmthm20
claim: Question 20(iii) separately asks whether the collision density of an arbitrary bracket expression is always rational.
strata_touched:
  - D5/S3/Arith/Density/RationalBracketCollisionDensity
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2603.10414

Primary version: https://arxiv.org/html/2603.10414v2#Thmthm20

Section 1 defines bracket expressions. Section 7, Question 20(iii), asks the
separate rationality question. The primary v2 HTML has 462659 bytes and
SHA-256 ba317318db8f71382c62bdea468c538f9abfe84ab3c84e31340af1d363b21cd3.

## Source statements

Section 1 defines a bracket expression on finitely many terms as
$w_n=\sum_{i=1}^t c_i\lfloor n\alpha_i\rfloor$, with integer coefficients
and positive rational moduli. Sequence indices include zero.

Question 20 defines $W=\{w_n:n\geq0\}$ and, for a positive integer $k$,
$C(k)=\{x\in W:x+k\in W\}$. Item (iii) asks, for an arbitrary bracket
expression, about
$\rho(k)=\lim_{N\to\infty}|C(k)\cap[0,N]|/N$ and explicitly asks:
“Is it always rational?”

## Mathematical answer and scope

The repository-derived theorem proves that this full limit exists and is
a rational real number for every finite number of terms, every integer
coefficient vector, every positive rational modulus vector, and every
positive integer shift. The count is over distinct nonnegative image
values, including both endpoints, with denominator N. Negative and zero
drift and the empty expression remain included.

Clearing the finitely many denominators gives an affine recurrence with
a positive index period and integer drift. Its actual image has an
eventually periodic nonnegative tail. Collision membership inherits this
period. The existing eventual-cycle average theorem then gives a rational
mean of a finite indicator cycle; the inclusive endpoint and denominator
are normalized to the stated limit. The source supplies the question and
definitions, not this proof.

The other characterisation, closed-form and game-theoretic requests in
Question 20 are outside this result. No extension to irrational moduli is
asserted.

## Literature qualification

The bounded source and literature screen is specified in
https://github.com/the-omega-institute/trureturing/issues/23511.
The v1 and v2 question and rational-modulus definition were read. Two
observed citing preprints, arXiv:2605.14321 and arXiv:2609.05358, were
screened for an answer, without a matching answer located. MathDB's first
20 displayed results for the source title, authors, source ID, and
collision/bracket/density queries did not identify an exact target record.
These readings were supplied by the source qualification; their full
searches have not been independently repeated here.

Citation coverage is incomplete: the source's OpenAlex count omitted two
observed citations, and further citation-service requests returned HTTP
429. General web and arXiv discovery also had documented capability gaps.
Exhaustive absence of a prior answer and global priority remain
ASSUMED-UNVERIFIED. A matching published answer excludes new-resolution
credit. No global novelty or priority claim is made.
