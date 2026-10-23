---
bibkey: gisin2017elegantjointmeasurement
authors: Nicolas Gisin
year: 2017
title: The Elegant Joint Quantum Measurement and some conjectures about N-locality in the Triangle and other Configurations
doi: null
url: https://arxiv.org/abs/1708.05556
claim: The elegant joint measurement and its singlet-triangle distribution are the physical literature inputs; the sourcewise noisy Born polynomial is verified separately in Lean.
strata_touched:
  - D5/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise
license: citation-only
triage: anchor
---

# Elegant joint measurement in a singlet triangle

Gisin's elegant joint measurement, Section II, equation (11), is the physical input for the four-outcome
two-qubit measurement in `ElegantJointMeasurementSourceNoise`. The four
tetrahedral directions specify a common singlet component and three Cartesian
triplet components. In the computational basis, the unnormalized vectors have
entries `sx + i sy`, `sz + 1`, `sz - 1`, and `-sx + i sy`; the effects are their
outer products multiplied by `1/8`.

Section III, equations (12)–(14), uses three independent singlet sources and the
cyclic outgoing/incoming wire order at each party. The outcome probabilities are
`25/256` when all labels agree,
`1/256` when exactly two agree, and `5/256` when all differ. Neither this table
nor a physical quantum realization alone proves classical triangle
incompatibility.

The Lean module constructs positive normalized density matrices and local
POVMs and derives the exact polynomial when the three sources are independently
mixed with `I/4`. Its three visibilities belong to the source matrices before
the tensor Born rule. The formal polynomial identity is not attributed as a
new physical measurement, and independent source noise is not identified with
a global mixture of the final output table.

## Verified locator

The original PDF at https://arxiv.org/abs/1708.05556, version v1 submitted
18 August 2017, identifies Nicolas Gisin and the title above. Page 2 contains
the EJM construction in Section II, equation (11), and the triangle table in
Section III, equations (12)–(14). The source proposes nonlocality as a conjecture
without proof; it is not a nonlocality certificate. The matrix identities and
noisy probability values claimed by this module are checked separately from
its explicit Lean definitions.
