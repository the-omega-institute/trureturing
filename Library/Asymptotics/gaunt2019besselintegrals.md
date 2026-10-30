---
bibkey: gaunt2019besselintegrals
authors: Robert E. Gaunt
year: 2019
title: Inequalities for some integrals involving modified Bessel functions
doi: 10.1090/proc/14433
url: https://arxiv.org/abs/1806.00524
claim: "Conjecture 2.4 asks for a sharp lower bound on a weighted modified-Bessel K tail."
strata_touched:
  - D5/S3/Analytic/GauntBesselTail/Result
license: citation-only
triage: anchor
---

# Gaunt's weighted Bessel tail conjecture

## Verified locator

https://arxiv.org/abs/1806.00524

R. E. Gaunt, *Inequalities for some integrals involving modified Bessel
functions*, Proc. Amer. Math. Soc. 147 (2019), 2937–2951,
DOI 10.1090/proc/14433. Conjecture 2.4 is on manuscript page 7 of
arXiv:1806.00524v2.

## Conjecture 2.4

> “Conjecture 2.4. Let n < 1. For ν ≥ 1 − n + √(2(1 − n)), define α_{ν,n} := ν + n − √((ν + n)² − 2ν − 1). Then, for all x > 0,
> ∫_x^∞ K_{ν+n}(t)/t^ν dt > K_{ν+n−α_{ν,n}}(x)/x^ν, ν ≥ 1 − n + √(2(1 − n)). (2.17)
> We have equality in (2.17) when n = 1, and this equality is valid for all ν ∈ ℝ. Let α′_{ν,n} := ν + n + √((ν + n)² − 2ν − 1), so that ν + n − α′_{ν,n} = −(ν + n − α_{ν,n}) and thus K_{ν+n−α′_{ν,n}}(x) = K_{ν+n−α_{ν,n}}(x). Then, the index ν + n − α_{ν,n} (and equivalently ν + n − α′_{ν,n}) in inequality (2.17) is best possible, in the sense that, for any β ∉ {α_{ν,n}, α′_{ν,n}}, either K_{ν+n−β}(x)/x^ν < K_{ν+n−α_{ν,n}}(x)/x^ν for all x > 0, or there exists a y > 0 such that ∫_y^∞ K_{ν+n}(t)/t^ν dt < K_{ν+n−β}(y)/y^ν.”

The quotation is the source statement. Lean uses the displayed definitions
and formulas in the result Scribe to encode the same parameter range,
inequality, equality case, and either/or optimality.

The integral representation of $K$ is recorded separately in
`D5/L/Asymptotics/nist2026dlmfbesselkintegral`, equation 10.32.9.
