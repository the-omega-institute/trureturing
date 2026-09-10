# Finite Proof-Carrying Sublevel Covers

## Abstract

A finite family of locally proved cover steps controls an arbitrary candidate space, including continuous phase spaces.

**Theorem 1.1 (Strictly ordered local proofs imply the complete sublevel cover).**

Lean statement: `D5/S0/Certificates/BoxCover/FiniteSublevelCover.sublevel_mem_target_of_local_steps`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/FiniteSublevelCover.sublevel_mem_target_of_local_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The LocalStep proof type records target inclusion, scalar residual exclusion, conserved residual-box exclusion, complete binary splitting and sublevel-preserving contraction. Every local premise is an actual proposition with a proof. Child indices must be strictly earlier. Strong induction then retains every candidate in the closed residual band until it reaches the target.

Only the proof nodes are finite. The candidate type may be uncountable, and the theorem does not replace it with observed roots or tube labels. Closed split boundaries are included; a contraction must preserve all sublevel points, not only exact zeros. Empty or overlapping target tubes and shared subtrees are permitted.

This is a logical assembly theorem. It is not a parser, an interval evaluator, or a proof that a concrete external trace satisfies LocalStep. The interval soundness, chart changes, actual seed identities and all local proof terms remain necessary for a concrete kernel-certified exclusion.

## References

- Truth anchor: `D5/S0/Certificates/BoxCover/FiniteSublevelCover.sublevel_mem_target_of_local_steps`
