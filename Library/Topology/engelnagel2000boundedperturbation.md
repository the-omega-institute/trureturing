---
bibkey: engelnagel2000boundedperturbation
authors: Klaus-Jochen Engel and Rainer Nagel
year: 2000
title: One-Parameter Semigroups for Linear Evolution Equations, Section III.1
doi: 10.1007/b97696
url: https://doi.org/10.1007/b97696
claim: Bounded perturbations admit the Dyson–Phillips expansion and the unique strongly continuous Duhamel evolution.
strata_touched:
  - D5/S3/Quantum/Analysis/DysonPhillipsPerturbation
license: citation-only
triage: anchor
---

# Bounded perturbations and the Dyson–Phillips expansion

Engel and Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Graduate Texts in Mathematics 194, Section III.1, is the classical reference
cited by the selected Lean source. No mathematical originality is claimed.

Roland Schnaubelt's *Evolution Equations*, Theorem 3.4, printed pages 74–76,
gives the Duhamel equations (3.5)–(3.6), the recursive Dyson–Phillips series
(3.7), absolute operator-norm convergence uniformly on compact time intervals,
and uniqueness among strongly continuous operator families solving (3.5).
Its proof gives the term estimate
`M^(n+1) * norm(B)^n * t^n * exp(omega*t) / n!`.
The contraction specialization uses `M=1` and `omega=0`.
The notes are available at
https://iana.math.kit.edu/downloads/iana3/schnaubelt/Skripten/evgl-skript.pdf.

The formal theorem constructs the evolution directly from a strongly
continuous contraction family and a bounded complex linear perturbation on
an arbitrary complex Banach space. It includes the zero space, extends time
by the identity on the nonpositive half-line, and proves uniqueness also for
individual curves continuous only on the specified closed interval. It does
not identify a generator or domain, assert operator-norm continuity in time,
or assert contractivity of the perturbed evolution.

The adapted Lean proof is Zayn Blore's
`zblore/csd-lean4@ca3edfd7a5576d6c4e188501f9abb7c3f38ccd7f`,
`CsdLean4/Mathlib/Analysis/Semigroup/BoundedPerturbation.lean`, restricted to
the core before its product-formula branch. The native real/NNReal
contraction-semigroup bundle supplies joint action continuity after scalar
restriction; the vector integrals and scalar-homogeneity proofs retain the
original complex maps. The full Apache-2.0 license is the existing
`docs/reports/qmutualinfo/csd-lean4-LICENSE.txt`, byte-identical to that
revision's LICENSE. The source root has no NOTICE file.

The donor uses Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; the receiving source uses Lean
4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Retire the adaptation when the repository's actually adopted Mathlib pin
supplies equivalent directly applicable Banach bounded-perturbation results.

## Verified locators

https://github.com/zblore/csd-lean4/blob/ca3edfd7a5576d6c4e188501f9abb7c3f38ccd7f/CsdLean4/Mathlib/Analysis/Semigroup/BoundedPerturbation.lean

https://iana.math.kit.edu/downloads/iana3/schnaubelt/Skripten/evgl-skript.pdf
