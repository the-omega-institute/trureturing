---
bibkey: beny2011simulation
authors: Cédric Bény and Ognyan Oreshkov
year: 2011
title: Approximate simulation of quantum channels
doi: null
url: https://arxiv.org/abs/1103.0649v3
claim: Fixed-state root-fidelity recovery optimization has an unrestricted complementary-channel dual, while the corresponding Kraus-bounded identity is a separate statement.
strata_touched: []
license: citation-only
triage: anchor
---

# Approximate simulation of quantum channels

Primary text: https://arxiv.org/pdf/1103.0649v3 .

Equations (54)–(55), printed pp. 5–6, state the root-fidelity purification
formula with unequal ancillary dimensions and its contraction form.
The definition preceding (56), p. 6, says explicitly that the fixed-input
quantity at an identity target is the square root of Schumacher
entanglement fidelity.

Corollary 5, (64)–(66), gives the unrestricted channel version and its
CPTP completion. Section IV, p. 11, (132)–(133), applies the duality at a
fixed physical input state. Equation (132) retains a bound on minimal
Kraus number; (133) is the unrestricted fixed-state identity. At an
identity target the complement can be the scalar trace, so its
postprocessing prepares an arbitrary common auxiliary density.

Sections 85 and 89 of
[recovery volume II](../../docs/develop/theory/AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II.md#85-the-three-environment-family-and-one-common-auxiliary-density)
use (133) for the fixed-input normalization and (54)–(55) inside the
two-state purification-midpoint calculation. Singular densities are
allowed. These applications do not restrict physical recovery Kraus
number or establish the remaining uniform numerical estimate.

The separate paper arXiv:0907.5391v4,
[General conditions for approximate quantum error correction and near-optimal recovery channels](beny2010approximate.md),
uses a worst-case-input fidelity in its main theorem. That theorem
does not replace the fixed-state equation (133) used here.
