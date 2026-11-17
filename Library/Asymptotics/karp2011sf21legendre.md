---
bibkey: karp2011sf21legendre
authors: Dmitry Karp
year: 2011
title: Log-convexity and log-concavity for series in product ratios of rising factorials and gamma functions
doi: null
url: https://math.nist.gov/~DLozier/SF21/SF21slides/Karp.pdf
claim: "Conjecture 4 extends the displayed Legendre Turán inequality to all positive real degrees and shifts strictly between zero and one."
strata_touched:
  - D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran
license: citation-only
triage: anchor
---

# Fractional-degree Legendre Turán inequality

## Verified locator

Source: https://math.nist.gov/~DLozier/SF21/SF21slides/Karp.pdf

NIST SF21 conference slides, physical PDF page 52, repeated on pages 53–54.
The deck acknowledges joint work with Sergei Sitnik and Sergei Kalmykov.
No arXiv identifier or numbered revision for this deck was located.
The source PDF SHA256 is
`f7aa6e10ba45df328bbbe244a44de685eb0e0016a8d4621e7d3b722db1e22293`.

## Source statement

> Curious open problems
>
> Turán (1946) inequality for Legendre polynomials:
>
> $${}_2F_1(-\mu,1+\mu;1;y)^2>{}_2F_1(-\mu-\delta,1+\mu+\delta;1;y){}_2F_1(-\mu+\delta,1+\mu-\delta;1;y),$$
>
> for $y\in(0,1)$, $\mu=1,2,\ldots$ and $\delta=1$.
>
> Conjecture 4
>
> Turán inequality is true for all $\mu>0$ and $0<\delta<1$.

## Mathematical correspondence

`GaussZeroBalanced.Defs.gauss` is Mathlib's ordinary real hypergeometric
function. The formal claim retains the displayed product order and quantifies
over real μ, δ and y with exactly the five strict inequalities quoted above.
It adds no positivity or zero-free hypothesis on the function values.

At μ=3/2, δ=63/64 and y=4095/4096, the three degrees are 33/64,
96/64 and 159/64. The proof uses 10,000-step rational recurrence
certificates with outward integer rounding and a geometric bound on the
remaining convergent series. The shifted values are negative and the central
value is positive; their shifted product exceeds the central square.

The experiment is in `the-omega-institute/trureturing-experiments`, commit
`33f936615612e4644068615c31c8777d6ba67ce5`, at
`docs/reports/fractional-legendre-turan/check.py`, SHA256
`5a108507a05370b53449cfc57e79e8904492499ce05065f3e9136b548b80012b`.
The recorded command is `python3 docs/reports/fractional-legendre-turan/check.py`
(exit 0). This is experimental evidence distinct from the Lean proof.

## Literature boundary

The partial literature screen is recorded in preregistration #23075.
Completeness is `ASSUMED-UNVERIFIED`. In particular, the full text of
Baricz–Rudrappa–Singh, DOI `10.1016/j.jat.2026.106319`, including
Theorems 2.4–2.5, remains unread. No global novelty claim is made.
The uniform moving-shift endpoint expansion, an infinite counterexample
family and positive-value variants remain open.
