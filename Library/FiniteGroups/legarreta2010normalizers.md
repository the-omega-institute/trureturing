---
bibkey: legarreta2010normalizers
authors: Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli
year: 2010
title: On the Number of Normalizers and Conjugacy Classes of Normalizers
doi: null
url: https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf
claim: Question 3.3 asks whether the centre index is bounded by the finite number of conjugacy classes of normalizers for groups satisfying the normalizer condition with strictly more normalizers than such classes.
strata_touched:
  - D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors
  - D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli
license: citation-only
triage: anchor
---

# Normalizers and centre index

## Verified locator

Source: https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf

International Journal of Algebra 4 (2010), no. 24, 1169–1175.
The journal version is the source; no arXiv identifier is recorded.

## Source statements

Printed page 1169:

> If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?

> NC: every proper subgroup H of G is properly contained in its normalizer N_G(H).

Printed page 1174:

> Question 3.3. Let G be a group satisfying the normalizer condition, and suppose that ω(G) is finite. If s(G) > ω(G), is |G : Z(G)| ω(G)-bounded? Is this true at least for finite p-groups?

## Scope

The target is the first, general-group question. A bound is a natural-valued
function of ω(G); the centre index is compared as a cardinal, so infinite
indices are retained. The finite-p-group question is separate.

The counterexamples are products of a fixed group of order sixteen and the
odd-prime modular group of order p³. Their normalizer counts are ten and
eight, and their centre indices are 8p². The fixed factor supplies the
strict gap between the two counts; the odd-prime factor supplies the
unbounded index.

The preregistration and limited literature screen are
https://github.com/the-omega-institute/trureturing/issues/27021.
Completeness of the literature screen is ASSUMED-UNVERIFIED: the paywalled
later full texts identified there were not read. The separate p-group
question, Question 3.2 and a bound taking arbitrary cardinal values remain
outside this settlement.

The independent finite checker is in
https://github.com/the-omega-institute/trureturing-experiments at commit
`ce5cb5acb1dc7013292f5e83e3f2f1c0c62ba8f7`, path
`docs/reports/legarreta-sica-tota-gavioli-2010-normalizer-centre-index/check.py`.
Its recorded SHA-256 is
`f3f27809964ac38b7a4c948aedf3556760974f54be365f863dfdfe55d7b8313a`;
`python3 check.py` exited 0 with `ALL_CHECKS_OK`, as reported in the
preregistration. The informal sentence about two noncentral lines is not
used: the recorded p=3 computation has three such subgroups, each with
normalizer order nine.
