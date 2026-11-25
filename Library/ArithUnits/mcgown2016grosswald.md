---
bibkey: mcgown2016grosswald
authors: K. McGown, E. Treviño, T. Trudgian
year: 2016
title: "Resolving Grosswald's conjecture on GRH"
doi: 10.7169/facm/2016.55.2.5
url: https://doi.org/10.7169/facm/2016.55.2.5
claim: "Section 3.2, in the proof of Theorem 3, gives the primitive-root sieve inequality."
strata_touched:
  - D5/S3/Arith/PrimitiveRoot/CharacterSieve
license: citation-only
triage: anchor
---

# The primitive-root sieve inequality

K. McGown, E. Treviño and T. Trudgian, *Resolving Grosswald's conjecture on
GRH*, *Functiones et Approximatio Commentarii Mathematici* **55**(2), 215–225.

Section 3.2, in the proof of Theorem 3, combines the e-free and te-free
characteristic functions. The coefficient of the principal character is
θ(e)δ. The nonprincipal coefficient bound yields the weighted primitive-root
lower bound. The implication from a positive smoothed von Mangoldt margin
to a prime primitive root is the corresponding weighted consequence;
no GRH assumption enters that implication or the finite sieve inequality.

For a nonnegative margin the coefficient sum divided by θ(e) is
K=δ(2^ω(e)−1)+(s−1+δ)2^ω(e). For a negative margin the absolute coefficient
mass instead has |δ| in its first term; call it K_abs. The lower bound with
signed K at negative δ is a mathematical consequence for nonnegative
weights by a separate nonnegativity argument. It is not an absolute error
estimate for arbitrary signed weights.

The public Lean weighted theorems allow signed weights, retain the complete
weighted defect and give two-sided error bounds: with K for δ≥0, and with
K_abs for all δ. The smoothed quantitative theorem retains the nonnegative
defect and both error sides after f=gcd(e,p−1). The existence theorem
requires θ(f)(δS−K_abs(f,U)M)+D_sm>0 and imposes no δ sign condition.

## Verified locator

DOI: 10.7169/facm/2016.55.2.5.
URL: https://doi.org/10.7169/facm/2016.55.2.5.
Locator: Section 3.2, proof of Theorem 3.
