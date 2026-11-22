---
bibkey: erdosnicolas1989functions
authors: P. Erdős and J.-L. Nicolas
year: 1989
title: "On functions connected with prime divisors of an integer"
doi: null
url: https://oeis.org/A330076
claim: "The conjecture on p. 390 states that the unordered sum of reciprocal positive divisor differences is less than the divisor count for every n > 5040."
strata_touched:
  - D5/S3/Arith/Divisors/ErdosNicolas/Basic
  - D5/S3/Arith/Divisors/ErdosNicolas/Classification
  - D5/S3/Arith/Divisors/ErdosNicolas/Main
license: citation-only
triage: anchor
---

# Erdős–Nicolas reciprocal divisor differences

P. Erdős and J.-L. Nicolas, “On functions connected with prime divisors of an integer”,
NATO ASI Series C **265** (1989), p. 390.
For positive divisors `d₁ < ⋯ < dτ(n)`, the quantity is
`Ĥ(n) = Σ_{i<j} 1/(dⱼ−dᵢ)`. The conjecture reads:

> We conjecture that for n > 5040, we have Ĥ(n) < τ(n).

The exact target is formalized by
`D5/S3/Arith/Divisors/ErdosNicolas/Basic.ErdosNicolasClaim`.
The definitions use rational reciprocals and the finite divisor count. General
kernel estimates and prime-power divisor blocks describe the reciprocal gap sum;
the source sentence supplies the problem, not a proof premise.

The unconditional theorem is
`D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas`.
Strong induction in `Classification.good_of_finite_certificates` uses the positive,
strictly smaller inputs `n/p` and `n/pᵃ`. Kernel estimates and prime-exponent
cutoffs reduce its remaining branches to six finite obligations. The imported
certificate modules prove the base interval, small and large exceptional lifts,
residue trees, main exponent box, and extra values. The same proved base cases
are supplied to both certificate families that depend on them. No finite
certificate proposition remains as a hypothesis of the unconditional theorem.

## Verified locator

Secondary catalog locator: https://oeis.org/A330076.
The quoted title, volume, printed page, and sentence identify the primary source.
No DOI or direct scan locator is asserted. The OEIS URL is a secondary reference,
not a primary full-text locator.
