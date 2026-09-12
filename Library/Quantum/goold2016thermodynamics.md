---
bibkey: goold2016thermodynamics
authors: John Goold, Marcus Huber, Arnau Riera, Lídia del Rio, Paul Skrzypczyk
year: 2016
title: The role of quantum information in thermodynamics — a topical review
doi: 10.1088/1751-8113/49/14/143001
claim: Relative entropy to a Gibbs state expresses the excess free energy.
strata_touched:
  - D5/S3/Quantum/Divergence/GibbsVariationalIdentity
license: citation-only
triage: anchor
---

# Relative entropy and Gibbs free energy

The review relates relative entropy to the free energy difference from a thermal
state. The repository uses natural logarithms and writes the dimensionless
Hamiltonian as H, so its Gibbs state is exp(H)/Tr(exp(H)). With physical energy K,
this corresponds to H = -beta K. The resulting identity is
log Z = ReTr(H rho) + S(rho) + D(rho || G).

## Verified locator

DOI: 10.1088/1751-8113/49/14/143001

URL: https://arxiv.org/abs/1505.07835

The arXiv abstract metadata was opened and identifies the title, authors, and
DOI above. The downloaded version is arXiv:1505.07835v3, dated 26 August 2016.
On PDF page 12, Example 1, “Free energy as a monotone,” explicitly displays
D(rho || tau(beta)) = Tr(rho(log rho - log tau(beta)))
= beta(F_beta(rho) - F_beta(tau(beta))). The example discusses diagonal qubit
states. Section V.D also identifies the relation between quantum relative entropy
and free energy. The definitions box on PDF page 5 gives the Gibbs state and
partition function and uses a base-two entropy convention.

This is a literature locator for the thermodynamic identity, not an attribution
of the repository's arbitrary-matrix Lean proof to that qubit example. The Lean
proof uses Mathlib's continuous functional calculus and the repository's existing
entropy decomposition, with natural logarithms throughout. No claim about
conversion rates, free energy monotonicity, or relative entropy nonnegativity is
formalized here.

## Verification record

Retrieved 2026-09-11: abstract and PDF returned HTTP 200. Byte counts and SHA-256
receipts are recorded in [历史记录](https://github.com/the-omega-institute/trureturing/blob/6c97ad12ce/docs/reports/gibbsvar-0911/implementation.md).
