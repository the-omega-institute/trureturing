---
bibkey: stasiuklutkenhaustan2025erasure
authors: Mikka Stasiuk, Norbert Lütkenhaus and Ernest Y.-Z. Tan
year: 2025
title: Quantum Chernoff divergence in advantage distillation for quantum key distribution and device-independent quantum key distribution
doi: 10.1103/PhysRevA.111.022631
url: https://arxiv.org/abs/2212.06975v3
claim: Equation (6) defines the full-public-flag conditional states; the paragraph after Theorem 2 conjectures a local operation that erases the error-state distinction while preserving both correct states.
strata_touched:
  - D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation
license: citation-only
triage: anchor
---

# Conditional error-state erasure

## Verified locator

DOI: 10.1103/PhysRevA.111.022631

Source: https://arxiv.org/abs/2212.06975v3

Section III A, PDF p. 5, paragraph immediately after Theorem 2.
Equation (6), PDF p. 2, gives the conditional state including the public bit.

## Source statement

> We remark that it does seem plausible to conjecture that Eve can indeed always perform an operation on her side-information such that this condition is fulfilled (while keeping the states $\rho_{ET|00},\rho_{ET|11}$ unchanged), because it essentially corresponds to having Eve “erase” her side-information whenever Alice and Bob did not get the same output value.

Equation (6) is

$$
\rho_{ET|ab} = \frac{1}{2} \sigma_{E|ab} \otimes \ket{0}\!\bra{0}_T + \frac{1}{2} \sigma_{E|\overline a \overline b} \otimes \ket{1}\!\bra{1}_T.
$$

Here the bar complements an outcome bit. The operation is one completely
positive trace-preserving map on ET, including the public bit, required to fix
both correct conditional states and identify the two error conditional states.
This differs from replacing the original attack by a different realization.

## Scope

The rational two-dimensional ensemble refutes that universal operational
assertion. Theorem 2 itself assumes coincident error states and is unaffected.
The physical preparation, Bell violation and Chernoff-region calculations are
exact experiment evidence, separate from the Lean refutation.

Literature completeness is ASSUMED-UNVERIFIED. The screened
Bhavsar–Moon–Bae arXiv:2602.05870v2 concerns neighbouring asymptotic key-rate
conditions; no assertion about its finite-blocklength or replacement-realization
questions follows from this refutation. The final journal full text has not
been independently compared with arXiv v3.
