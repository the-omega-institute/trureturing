---
bibkey: lazardrouillier2007parametric
authors: Daniel Lazard and Fabrice Rouillier
year: 2007
title: Solving parametric polynomial systems
doi: 10.1016/j.jsc.2007.01.007
claim: Away from a discriminant variety, a parametric polynomial system has the analytic covering property; in particular finite root cardinality is locally constant and each sheet projects locally diffeomorphically to parameter space.
strata_touched:
  - D5/S3/Quantum/Tomography/CayleyCoverAnalysis
  - D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion
license: citation-only
triage: anchor
---

# Solving parametric polynomial systems

Lazard and Rouillier develop discriminant varieties for parametric constructible
and semialgebraic polynomial systems. The central structural statement used by
the MUB-six lane is that, off the discriminant variety, the solution set over a
parameter neighborhood has an analytic covering structure: the finite number
of roots is constant and the projection is locally a diffeomorphism on each
sheet.

This is the correct literature analogue of the next strict-X step. After the
five dephased unit phases are written in signed Cayley coordinates, clearing the
positive denominators makes the common-unbiased equations polynomial in the
five phase variables and the two real strict-X parameters. The bad parameter
set is therefore naturally split into:

- a root discriminant, where a common-unbiased zero is singular or escapes a
  chosen affine chart;
- an edge discriminant, where two continuously labelled root sheets acquire a
  new zero inner product;
- the Hadamard-branch discriminant already present in the order-six matrix
  parameterization.

On a connected parameter cell avoiding the first discriminant, the number of
common-unbiased roots cannot change. Avoiding the relevant edge discriminants
then preserves the certified orthogonality supergraph up to deletion of allowed
edges. This reduces repeated five-dimensional global root traversal to a
lower-dimensional parameter-space exclusion problem.

The repository does not import the paper as an axiom. `CayleyCoverAnalysis`
formalizes elementary quantitative consumers: local uniqueness, root migration,
and a uniform residual barrier. A future discriminant-cell theorem must still
connect the actual strict-X polynomial system to these hypotheses inside Lean.

## Verified locator

- DOI: https://doi.org/10.1016/j.jsc.2007.01.007
