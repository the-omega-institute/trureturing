---
bibkey: crossley2026perfectpowers
authors: Lee Crossley
year: 2026
title: A prime-window criterion for RH on perfect powers
doi: 10.5281/zenodo.24411621
url: https://doi.org/10.5281/zenodo.24411621
claim: For every fixed positive integer k, RH is equivalent to a one-sided bound on a weighted ordinary-prime sum at every kth power in arbitrarily late blocks of indices.
strata_touched: []
license: citation-only
triage: anchor
---

# Perfect-power samples

Omega tests its centred cumulative Mangoldt sum $U$ at both endpoints and the fourth powers in arbitrarily late intervals $[Y,Y^b]$. Crossley tests an ordinary-prime tent at every $n^k$ with $K\le n\le K^2$ for arbitrarily large $K$ and any fixed positive integer $k$. The corresponding prime-power deficit in Crossley’s notation satisfies $D(x)=-U(x)+3U(x/2)-2U(x/4)$. The identity follows by expanding each Mangoldt ramp. [Omega’s finite-window theorem](https://github.com/the-omega-institute/trureturing/blob/dc35da3902f250514519ed960fda01179fc42159/D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.lean#L267), [Crossley’s definitions and theorem](https://github.com/leecrossley/prime-window-power-samples/blob/b350c9c8fb73fbeeadfac0fd3662d6a262e6f8c5/README.md#L16).

The earlier square-sampling argument for the ordinary-prime tent is due to bramble_trace. Crossley extends it to every fixed power by bounding the change between consecutive samples in terms of the supremum of the real parts of the zeta zeros. [bramble_trace’s proof](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24), [Crossley’s fixed-power result](https://doi.org/10.5281/zenodo.24411621).
