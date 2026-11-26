---
bibkey: cohen2015grosswald
authors: S. D. Cohen, T. Oliveira e Silva, T. S. Trudgian
year: 2015
title: "On Grosswald's conjecture on primitive roots"
doi: 10.4064/aa8109-12-2015
url: https://doi.org/10.4064/aa8109-12-2015
claim: "Section 3 develops the characteristic-function sieve for primitive roots."
strata_touched:
  - D5/S3/Arith/PrimitiveRoot/CharacterSieve
license: citation-only
triage: anchor
---

# A character sieve for primitive roots

S. D. Cohen, T. Oliveira e Silva and T. S. Trudgian,
*On Grosswald's conjecture on primitive roots*, *Acta Arithmetica*.

Section 3 supplies the characteristic-function sieve. For a divisor e of p−1,
the remaining prime factors contribute the margin δ = 1−Σ 1/t. Combining
the e-free and te-free characteristic functions gives a lower bound for
the primitive-root characteristic function. For nonnegative weights, dropping
the nonnegative defect gives a mathematical lower-bound consequence; when
the margin is nonpositive, a separate nonnegativity argument applies to
that consequence.

The public Lean statements distinguish this consequence from the full
signed-weight estimate. They allow every real weight and retain its weighted
defect, which can have either sign. The signed coefficient K gives a
**two-sided** error bound when δ≥0. The absolute coefficient K_abs replaces
δ by |δ| in its first term and gives the two-sided bound for every δ.
The smoothed existence criterion uses K_abs at f=gcd(e,p−1) and retains the
nonnegative smoothed defect in its strict positivity hypothesis.

## Verified locator

DOI: 10.4064/aa8109-12-2015.
URL: https://doi.org/10.4064/aa8109-12-2015.
Locator: Section 3.
