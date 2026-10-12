---
bibkey: goodmeddaugh2020shadowing
authors: Chris Good and Jonathan Meddaugh
year: 2020
title: Shifts of finite type as fundamental objects in the theory of shadowing
doi: 10.1007/s00222-019-00936-8
url: https://doi.org/10.1007/s00222-019-00936-8
claim: The final journal Theorem 8 proves preservation of shadowing by arbitrary directed compact Hausdorff Mittag-Leffler inverse limits, allowing nonsurjective bonding maps.
strata_touched: []
license: citation-only
triage: anchor
---

# Inverse limits and finite-cover shadowing

The journal identity is Inventiones mathematicae 220(3), 715–736,
DOI 10.1007/s00222-019-00936-8. The inspected final journal body has 22 pages,
with Theorem 8 on printed pp.722-723. Definitions 2 and 3, pp.719-720,
require arbitrary directed indices, compact Hausdorff stages, continuous
coherent bonding maps and equivariant continuous stage dynamics; the bonds
are not required to be onto. Definition 4, p.720, imposes the exact image
stabilization condition. Definition 7, p.722, defines finite-open-cover
shadowing on nonempty compact Hausdorff spaces.

Theorem 8 states: "Let f : X → X be conjugate to an ML inverse system
consisting of maps with shadowing on compact spaces. Then f has shadowing."
Its proof shadows at an image-stabilizing finer stage, projects the tracing
point to a coarser stage, and lifts that coarse point to the full limit.

Primary custody: the published PDF and its page-delimited `pypdf` extraction
are preserved in the cross-domain research workspace. The extraction SHA256
is `094ed9c8311312e7070789c042d7a57e2b7b94d08d9c21db07ab2b0aa6e06b2e`.

For comparison, arXiv:1702.05170v1, 16 February 2017, Definitions 2 and 3
impose compact Hausdorff stages, arbitrary
directed indices, continuous **surjective** coherent bonding maps, and
continuous equivariant stage dynamics. Definitions 4 and 6 give
finite-open-cover shadowing; Definition 6 explicitly requires a nonempty
space. The inverse-limit preservation result is v1 Theorem 7. V1
Theorems 17 and 18 describe totally disconnected shadowing systems via SFT
inverse limits, with the sequence characterization in the metric case.
These numbers are not asserted for the final article.

The self-contained formal theorem
`D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.shadowing_inverse_limit_of_mittag_leffler`
implements the final journal's nonsurjective image-stabilized argument in
Lean over cofiltered thin categories. It shadows on an unreduced finer stage
and lifts only the projected coarse point. It also handles empty stages
vacuously. The core preservation theorem is attributed known background,
not a new mathematical result or a settlement of Peng's construction question.

## Verified locator

Primary final journal source: https://doi.org/10.1007/s00222-019-00936-8.
DOI: 10.1007/s00222-019-00936-8.

Inventiones mathematicae 220(3), pp.715–736. Theorem 8 is on printed
pp.722–723; Definitions 2–4 on pp.719–720 specify compact Hausdorff
stages, arbitrary directed indices and Mittag-Leffler image stabilization.
The final-journal theorem, rather than the surjective-bond v1 theorem, is
the cited inverse-limit preservation result.
