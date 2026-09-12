---
bibkey: mathlib2026irreducibleschur
authors: Stepan Nesterov and the mathlib community
year: 2026
title: Irreducible representations and scalar intertwining endomorphisms
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RepresentationTheory/Irreducible.lean
claim: Schur's lemma makes every equivariant endomorphism of a finite-dimensional irreducible complex representation scalar; Hermitian matrices force a real scalar and trace-one probes agree.
strata_touched:
  - D5/S3/Quantum/Matrix/CrossSpeciesConsensus
license: Apache-2.0
triage: anchor
---

# Irreducible complex representations

## Verified locator

The exact upstream locator is:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RepresentationTheory/Irreducible.lean

The source at the pinned revision was opened from GitHub's raw endpoint (HTTP 200).
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`
is Schur's lemma in the unbundled representation API: scalar inclusion into the
intertwining endomorphism algebra is bijective. Its assumptions are irreducibility,
finite dimension, and an algebraically closed scalar field. The categorical formulation
also exists as `CategoryTheory.endomorphism_simple_eq_smul_id`, with the
finite-dimensional representation category supplied by `FDRep`.

The D5 specialization transports a complex matrix group action to linear maps,
uses this upstream result, and restricts the resulting complex scalar to the reals
using Hermitian diagonal entries. The trace-one corollary follows by trace linearity.
This is a conditional mathematical result. Shared active symmetry and irreducibility
are supplied hypotheses; the source does not establish them for physical probes.
