# Zero Geometry Beneath Weil Positivity

## Theorem: A projected zero does not erase the labeled vector

Provenance: `repo-derived`

Statement: `D5/S3/Weil/ZeroGeometry.projection_zero_labeled_vector_spec` `✓ std3`

A supplied classical zeta zero is retained alongside nonvanishing of its labeled coefficient function for every additive ledger. The scalar zero is an explicit hypothesis, so the declaration proves no zero exists. No analytic projection operator is defined, and no projection identity outside the Dirichlet convergence half-plane is claimed. On the O-6 path, this prevents cancellation in zeroSum from being mistaken for vacuous disappearance of the labeled data.

## Theorem: Positive-length entries detect off-line displacement

Provenance: `repo-derived`

Statement: `D5/S3/Weil/ZeroGeometry.off_line_scaling_entry_spec` `✓ std3`

At every positive-length coordinate, the scaling entry is displacement from real part one half times ledger length. It is nonzero exactly off the critical line, positive to the right, and negative to the left. The explicit positivity hypothesis replaces the source ledger's concrete nonzero-address fact and strengthens the sign assertions to equivalences. The source's coefficient factorization, unbounded-ray clause, and rotation-invariance clause are not formalized here. This entry is the local quantity that an eventual O-6 positivity-to-balance argument must force to zero.

## Theorem: A global factor cannot clear off-line scaling

Provenance: `repo-derived`

Statement: `D5/S3/Weil/ZeroGeometry.global_factor_clearing_forces_critical_line` `✓ std3`

For a nontrivial additive ledger, if one complex factor makes every half-density reading have norm one, then the parameter has real part one half. The factor is arbitrary and independent of the coordinate; exact unit norm at every coordinate is the calibrated premise. The governance claim excluding an address-dependent inverse register is not part of this theorem. Thus O-6 positivity cannot be replaced by a single global normalization shortcut.

## Theorem: ZeroData symmetries form the mirror quartet

Provenance: `repo-derived`

Statement: `D5/S3/Weil/ZeroGeometry.zero_quartet_scaling_spec` `✓ std3`

The declaration is conditional on a supplied ZeroData value. Its zero_conjugation and zero_reflection fields are premises carrying the first two displayed equalities, rather than conclusions derived from real coefficients, analytic continuation, or a functional equation. ZeroData also requires a duplicate-free exhaustive enumeration of all classical nontrivial zeta zeros, exact multiplicities, reflection and conjugation permutations, their multiplicity-preservation laws, and local finiteness. The repository does not prove that ZeroData is inhabited: no instance or example exists. Accordingly this conditional declaration does not close the source theorem; that source obligation remains open. From the supplied fields Lean derives only the composed mirror equality and its algebraic reversal of every scaling entry. It proves neither pairwise distinctness nor the source's nonmultiplicative numerical instrument, and the conditional cancellation alone supplies no positivity.

## Theorem: Mirror partners cancel across distinct positions

Provenance: `repo-derived`

Statement: `D5/S3/Weil/ZeroGeometry.mirror_pair_distinct_iff_off_line_and_cancels` `✓ std3`

A parameter differs from its conjugate reflection exactly when it is off the critical line, yet their scaling entries sum to zero at every coordinate. This is generalized from the concrete prime-log ledger to every additive ledger. Cross-position cancellation does not imply local balance at either position. It isolates why the convolution-square positivity quantified by O-6 must add information beyond zero-set symmetry.

## Definition: An ontological zero records projection, balance, and closure

Provenance: `repo-derived`

Statement: `D5/S3/Weil/ZeroGeometry.IsOntologicalZero` `✓ std3`

The predicate conjoins a classical zeta zero, vanishing of every local scaling entry, and a carried closure-level condition. The projection clause is represented by classicalZeta rather than a separately defined analytic projection. The closure condition is carried as the arbitrary predicate closedAt; no inhabitant is asserted. This names the local-balance target for the open implication beneath O-6 without assuming it.

## Theorem: Ontological local balance forces the critical line

Provenance: `repo-derived`

Statement: `D5/S3/Weil/ZeroGeometry.ontological_zero_re_eq_critical` `✓ std3`

Given one nonzero ledger-length coordinate, the local-balance conjunct of an ontological zero forces its real part to one half. The abstract witness replaces the source's concrete log-two coordinate, and no property of the carried closure predicate is used. The missing implication from every projected zero to local balance is exactly the open O-6 bridge. This theorem closes only the final algebraic edge after that bridge.
