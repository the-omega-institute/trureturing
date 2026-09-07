# Finite Partial-Signature Completion

## Abstract

For normalized finite partial-signature requirements over nonempty output and return types, the minimum completion size is the full-pair count plus the larger residual count.

**Definition 1.1 (Normalized partial-signature requirements).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.Requirements`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.Requirements` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For output, return-class, full-pair, output-only, and return-only types in one universe, Requirements stores embeddings of full indices into output-return pairs and of residual indices into their respective coordinate types. Every residual output differs from every full pair's output, and every residual return differs from every full pair's return. The structure itself assumes neither finiteness nor nonemptiness of these types.

**Definition 1.2 (The required signature count).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.requiredSignatureCount`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.requiredSignatureCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For normalized requirements with finite Full, OutputOnly, and ReturnOnly index types, requiredSignatureCount is the cardinality of Full plus the maximum of the cardinalities of OutputOnly and ReturnOnly. This definition depends only on those three cardinalities and does not assume that the output or return-class type is nonempty.

**Definition 1.3 (A finite injective completion).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.Completion`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.Completion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For normalized requirements, a Completion supplies a state type in the same universe, a Fintype instance on it, and an embedding of states into output-return pairs. Its three witness maps realize every full pair exactly, every residual output in the first coordinate, and every residual return in the second coordinate. Injectivity of the witness maps is not a separate field, and the structure does not require every state to be a witness.

**Theorem 1.4 (An optimal completion exists).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.exists_optimal_completion`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FinitePartialSignatureCompletion.exists_optimal_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized requirements with finite Full, OutputOnly, and ReturnOnly index types and with both Output and Class nonempty, there exists a completion whose state cardinality equals requiredSignatureCount. The construction retains every full pair, pairs residual requirements by finite indices, and fills unmatched coordinates with chosen defaults; it does not assert uniqueness of the resulting completion.

**Theorem 1.5 (The exact minimum completion size).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.finite_partial_signature_completion_exact`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FinitePartialSignatureCompletion.finite_partial_signature_completion_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized requirements with all three index types finite and with nonempty output and return-class types, requiredSignatureCount is a lower bound for the state cardinality of every completion and is attained by some completion. Thus the full-pair count plus the maximum of the two fresh residual counts is the exact minimum under these hypotheses.

**Definition 1.6 (Outputs present in full signatures).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.outputProjection`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.outputProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set of output-return pairs and decidable equality on Output, outputProjection is its finite-set image under the first-coordinate map. It contains precisely the outputs occurring in the full signatures, with repeated output values represented only once.

**Definition 1.7 (Returns present in full signatures).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.returnProjection`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.returnProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set of output-return pairs and decidable equality on Class, returnProjection is its finite-set image under the second-coordinate map. It contains precisely the return classes occurring in the full signatures, with duplicate return values removed by the finite-set image.

**Definition 1.8 (Uncovered output requirements).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.residualOutputs`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.residualOutputs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite set of full signatures, a finite set of required outputs, and decidable equality on Output, residualOutputs is the required output set minus outputProjection of the full signatures. It retains exactly those requested outputs that do not already occur in a full pair.

**Definition 1.9 (Uncovered return requirements).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.residualReturns`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.residualReturns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite set of full signatures, a finite set of required return classes, and decidable equality on Class, residualReturns is the required return set minus returnProjection of the full signatures. It retains exactly the requested returns not already covered by a full pair.

**Definition 1.10 (Normalize finite-set requirements).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.requirementsOfFinsets`

*Formalization.* `D5/S0/Automata/FinitePartialSignatureCompletion.requirementsOfFinsets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For output and return-class types with decidable equality, finite sets of full signatures, requested outputs, and requested returns determine normalized Requirements. The index types are the subtypes of the full set and the two residual sets, and all three embeddings are subtype inclusions. Removing the full projections ensures the required freshness; neither coordinate type must be nonempty for this normalization.

**Theorem 1.11 (The finite-set count formula).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.requiredSignatureCount_requirementsOfFinsets`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FinitePartialSignatureCompletion.requiredSignatureCount_requirementsOfFinsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite sets of full signatures, required outputs, and required returns over coordinate types with decidable equality, requiredSignatureCount of requirementsOfFinsets equals the full set's cardinality plus the maximum of the cardinalities of residualOutputs and residualReturns. This is an identity of counts and requires no nonemptiness assumption.

**Theorem 1.12 (The exact minimum for finite-set requirements).**

Lean statement: `D5/S0/Automata/FinitePartialSignatureCompletion.finite_partial_signature_completion_finsets`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FinitePartialSignatureCompletion.finite_partial_signature_completion_finsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty Output and Class types with decidable equality, let the normalized requirements come from any finite sets of full signatures, requested outputs, and requested returns. Every completion of these requirements has at least the full set's cardinality plus the maximum of the two residual-set cardinalities states, and some completion has exactly that many. Residuals remove values already in the full projections; the ambient coordinate types need not be finite.

## References

- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.Completion`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.Requirements`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.exists_optimal_completion`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.finite_partial_signature_completion_exact`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.finite_partial_signature_completion_finsets`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.outputProjection`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.requiredSignatureCount`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.requiredSignatureCount_requirementsOfFinsets`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.requirementsOfFinsets`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.residualOutputs`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.residualReturns`
- Truth anchor: `D5/S0/Automata/FinitePartialSignatureCompletion.returnProjection`
