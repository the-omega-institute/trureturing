---
bibkey: baezduarte2003criterion
authors: "Luis Báez-Duarte"
year: 2003
title: "A new necessary and sufficient condition for the Riemann hypothesis"
doi: null
url: "https://arxiv.org/abs/math/0307215v1"
claim: "Equation (1.5), Lemma 1.1 and the compact-convergence argument of Proposition 2.1 motivate normalized Pochhammer bounds and an actual-coefficient summable majorant; the initial half-plane Newton reciprocal-zeta identity is proved using the coupled unsigned kernel."
strata_touched:
  - D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds
  - D5/S3/Analytic/SeriesInequalities/BaezDuarteNewtonMajorant
  - D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds
  - D5/S3/Weil/Analytic/BaezDuarteNewton
  - D5/S3/Weil/Analytic/BaezDuarteContinuation
license: "No license assertion is made; this note records mathematical facts and bibliographic metadata only."
triage: anchor
---
<!-- GID: D5/L/Analytic/baezduarte2003criterion -->
# Normalized products and compact convergence

## Verified locator

- URL: https://arxiv.org/abs/math/0307215v1

https://arxiv.org/abs/math/0307215v1 is the retained primary version.
The registered PDF extraction locates equation (1.5), Lemma 1.1, and
Proposition 2.1 on PDF page 2, printed page 2. This worker uses that recorded
source evidence; it does not claim a new online metadata verification.

## Source scope and local refinements

The retained primary record is version 1, published and updated
2003-07-16T03:11:19Z. The record supplies neither a journal reference nor a DOI.
The retained six-page PDF has SHA256
`3d0bd39e223561516a617b437274409112ff31b5488b8214fff749c3e00e8d34`.

On printed page 2, equation (1.5) defines the product of the factors
`1 - s/r` for `r = 1,...,k`. Equation (1.6) identifies its binomial notation.
Lemma 1.1 states that each open disk admits a positive unspecified constant
bounding the product by that constant times `k^(-Re(s))`.

The local producer is a **repo-derived quantitative refinement**: for every
nonnegative radius R, every k at least one, and every complex z with norm at
most R, it uses the explicit constant `exp(R + R^2)`. Neither this explicit
constant nor this closed-disk formulation is printed in Lemma 1.1. The
normalization and zero-index companions are repo-derived algebraic bridges
using pinned mathlib's descending Pochhammer polynomial. They do not prove a
full generalized complex-binomial bridge.

Proposition 2.1, also on printed page 2, assumes every-positive-epsilon decay
with exponent `-3/4 + epsilon/2`, identifies the series with reciprocal zeta on
the open half-plane `Re(s) > 1/2`, and states uniform convergence on its compact
subsets. The local consumer is a **repo-derived proof refinement** of that
compact-convergence argument: under the stated every-epsilon decay with
exponent `-3/4 + epsilon`, it constructs an all-index nonnegative summable
majorant for the actual repository coefficients. Rescaling epsilon relates the
two hypotheses, but that source correspondence does not assert the full
proposition. No reciprocal-zeta identity or RH direction is proved here.

The zero index and every finite-prefix term are retained. No nonpole,
nonvanishing, real-only or nonempty-compact hypothesis is imposed. The printed
positive 3/4 on page 5 and the Lemma 2.2 cross-reference are not silently
corrected by this note.

Source standing: user-requested formalization of known literature, with the
above repo-derived refinements. The retained public search is bounded; later
and unread literature remains unknown. Oracle access was unavailable, so no
Oracle validation, model diversity, exhaustive search, or newest-literature
certainty is claimed. TauCeti and Formalpedia are search-only sources.

## Original Q and unconditional coefficient bound

Lemma 2.1 on printed page 3 defines the unsigned series in (2.2), starting
at the positive integer one, and states the half-power order bound (2.3).
Remark 1.1 on page 1 states unconditional half-power decay of the actual
coefficients. Equation (2.7) on page 4 gives their signed Mobius series;
equation (2.8) and the subsequent double-series discussion use the unsigned
series to justify a Newton interchange. The latter discussion cites Lemma 2.2
as printed; the Q estimate is actually labeled Lemma 2.1. This distinction is
retained, not silently repaired. The PDF bytes above were reopened for this Q
implementation, and printed pages 1, 3, 4 and 5 were inspected directly.

BaezDuarteQBounds uses the exact unsigned series with index n shifted to n+1.
Its explicit bound 3/sqrt(k+1), for every natural k including zero, is a
**repo-derived quantitative refinement**, not the literal source's unspecified
constant. The finite geometric estimate on the closed unit interval, and the
finite split N/(k+1)+1/N for every positive natural N and every endpoint M,
are repo-derived proof refinements. The split includes M<N and retains every
original summand. Its square-root cutoff gives the all-index bound; thin
companions give 3*k^(-1/2) for k>=1 and Q(0)<=2. The actual frozen coefficient
owner and its existing Mobius HasSum give |c(k)|<=Q(k), hence unconditional
coefficient bounds. No second arithmetic definition is introduced.

The source uses Euler-Maclaurin and Gamma asymptotics; those arguments and
constants are not claimed to have been transcribed by the finite-split proof.
Neither an original Newton HasSum/interchange/Dirichlet identification nor
holomorphic extension nor either RH direction is established by this module.
The reviewed P and compact-majorant content above remains unchanged in scope.


## Newton identity on the initial half-plane

The double-series argument around equation (2.8), printed page 4 of the same
https://arxiv.org/abs/math/0307215v1 source, identifies the Newton series with
reciprocal zeta initially for Re(s)>1. BaezDuarteNewton now proves this precise
initial-domain HasSum for the existing actual coefficients and normalized
Pochhammer polynomials evaluated at s/2. This new owner does not change the
historical scope statements about the three earlier modules above.

The proof is a **repo-derived implementation** of that identification. It
combines the frozen Q and P estimates into a summable unsigned coupled kernel,
with strict outer exponent -(Re(s)+1)/2 below -1. Eventual comparison keeps the
entire finite prefix. The absolute Moebius bound supplies the signed kernel's
absolute summability; this is derived from Re(s)>1, not imposed as a premise.
The frozen signed coefficient HasSum and pinned mathlib's complex binomial
series evaluate the two families of fibers. Positive-real-base complex-power
identities and the existing Moebius Dirichlet product identify the sum with
1/riemannZeta(s). The zero arithmetic row is one, P(0,z)=1, P(1,z)=1-z, and
s=2 leaves only the original coefficient c(0).

The full Proposition 2.1 continuation to Re(s)>1/2 under every-epsilon decay,
holomorphic extension, and both RH directions remain outside this theorem.
The source's printed positive 3/4 and Lemma 2.2 reference caveats remain as
recorded above. No new primary-source access, successful Oracle participation,
or exhaustive literature search is claimed by this implementation.

## Continuation under the original decay assumption

BaezDuarteContinuation proves the continuation and compact uniformity of
Proposition 2.1 under every-positive-epsilon coefficient decay, together with
the sufficiency direction of Theorem 1.1. The finite complex coefficients are
bound to the existing real coefficients using even-zeta realness. Rescaling
epsilon explicitly binds the two printed decay conventions.

The holomorphic sum is identified with `(s-1)/riemannZeta₁(s)` on the whole
open half-plane Re(s)>1/2. At one it is zero. Off one it agrees with the raw
reciprocal zeta. All compact subsets, including those containing one, have
uniform convergence of the actual range partial sums. Analytic uniqueness
applied to the entire multiplier supplies the product identity and excludes
zeros in the right half of the critical strip; the existing reduction then
yields standard RH. These are literature-attested statements with a
repo-derived implementation through public mathlib analytic continuation APIs.

The six original paper pages were read for this continuation. Theorem 1.1 and
Proposition 2.1 print the negative exponent; the page 5 proof paragraph prints
positive 3/4. The negative exponent is used in the proof. Page 5 also prints
a positive Abel-integral sign and a shifted transformed kernel; the actual
coefficient requires the negative derivative integral at its actual index.
The square substitution in the beta integral requires a factor 1/2. These
are recorded mathematical corrections, not an author-issued erratum. No
unproved printed identity is imported as a hypothesis. The Abel and beta
transfer and the RH necessity direction are not claimed by this continuation
module. Earlier module scope statements above remain historical and exact.
