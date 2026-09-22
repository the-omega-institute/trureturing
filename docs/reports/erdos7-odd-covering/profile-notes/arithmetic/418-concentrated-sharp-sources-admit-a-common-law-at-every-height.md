[Index](../../marked_head_profile.md) · [Source and fixed recipe](414-same-projection-transport-controls-concentrated-sharp-sources.md) · [Independent-phase separator](416-exact-independent-layout-tree-separation-and-actual-laws.md) · [Analytic tail](417-prefix-local-disagreement-extends-the-same-law-to-height-seven.md)

# Concentrated sharp sources admit a common law at every height

For every integer K>=2, the explicit concentrated sharp source R_K
defined in report 414 admits a probability supported on R_K such that

    Gamma_K(nu) = max_lambda E_nu ell_lambda^2 < 2t_K,
    t_K = 3-(K+2)3^-K.

The probability is selected before lambda, which retains every
independent phase at every original divisor of 5*7^K. This closes the
remaining two finite heights of that particular family. It does not
settle arbitrary sharp minimum sources, arbitrary one-surplus tails,
or unrestricted Erdős #7.

The result combines analytic proofs with exact finite integer dynamic
programming; no Lean certification is claimed.

## The original fixed recipe succeeds at heights five and six

Use the actual full-five and pair-ternary probabilities from 414:

    nu_K = (5/13)mu_K + (8/39)(eta_23 + eta_24 + eta_34).

The source, component choices and coefficients are unchanged. Applying
the full independent-layout recurrence proved in 416 gives:

| K | Source points | Exact Gamma_K(nu_K) | Target 2t_K | Strict margin |
|---|---:|---|---|---|
| 5 | 3127 | 34250057/5923125 | 1444/243 | 947443/5923125 |
| 6 | 15627 | 502738967/88846875 | 4358/729 | 28392283/88846875 |

For K=5, one attaining original layout, in increasing divisor order, is

    divisors: 1,5,7,35,49,245,343,1715,2401,12005,16807,84035
    phases:   0,2,3,17,17,17,115,1487,801,3202,5603,39217.

For K=6, retain these phases and add

    a_117649 = 39217,  a_588245 = 39217.

Literal CRT evaluation gives the displayed expectation in each case.
It supplies attainment only; the upper bound comes from the exact
recurrence over all independently named original labels. Neither
an aligned-layout restriction nor an approximate optimizer supplies
the maximum.

## Combining all heights

Select one actual probability by the following cases:

* K=2: the source is the height-two member of 412, because its clean
  tails have height one and hence are monochromatic. That report's
  uniform full-five law, choosing row four at the two duplicated leaves,
  has bound 126/25 and target margin at least 16/225.
* K=3,4: use the explicit rational probabilities in 416. Their respective
  maxima are 559/100 and 2843/500, with margins 107/2700 and 2239/13500.
* K=5,6: use the original fixed recipe and the exact maxima above.
* K>=7: use that same fixed recipe. The analytic prefix-local transport
  theorem in 417 gives margin at least 1/15 at every such height.

These cases exhaust the integer domain K>=2. In fact every margin
listed above is at least 107/2700, so this selection gives the uniform
family bound

    for every K>=2, there exists nu_K supported on R_K,
    for every original independent layout lambda,
    E_(nu_K) ell_lambda^2 <= 2t_K - 107/2700.

The finite checks do not justify the unbounded quantifier by themselves;
the proof for K>=7 does. The recipe fails at K=2,3,4 as recorded in 414
and 416, which is why the choice of probabilities at those heights is
explicitly different. No optimality of the supplied source laws is claimed.

## Reproduction

[`concentrated_fixed_recipe_separation.json`](../../frontier/cover-geometry/concentrated_fixed_recipe_separation.json)
stores the two exact values, targets and full attaining phase maps.
The actual probabilities are reproduced from 414's existing constructor,
not copied as large floating-point arrays.

[`concentrated_fixed_recipe_separation.py`](../../frontier/cover-geometry/concentrated_fixed_recipe_separation.py)
accepts any finite list of heights and claimed maxima under the same
schema. It reuses the actual-family validator, checks normalization and
support, independently evaluates each literal CRT witness, and runs
the exact separator. It reports the signed target margin, so a supplied
failure case is not silently reclassified as success. Resource limits
raise errors instead of returning partial maxima.

From the repository root:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/concentrated_fixed_recipe_separation.py --max-states 40000000 --max-operations 500000000

The height-five solve used 2,506,914 cached states and 37,204,064 subset
convolution candidates. Height six used 24,706,914 states and 468,024,276
candidates. These are exact arithmetic computations, with unbounded
integer scores. The operation limit counts subset candidates only,
not total work or memory. The fixed-law certificates and the general
recurrence have distinct roles; neither is a theorem about all sources.
