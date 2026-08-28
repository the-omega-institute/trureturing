# Acyclic Source-Formula Correctness

## Abstract

Acyclic source formulas hold exactly when a source-supported proof exists.

**Theorem 1.1 (Source formulas are correct for valid proofs).**

$$\begin{aligned}\forall S: \operatorname{Type}, [\operatorname{DecidableEq}(S)], n: \mathbb{N},\\G: \operatorname{SourceProofGraph}(S, n), A: \operatorname{Finset}(S), c: \operatorname{Fin}(n),\\\operatorname{sourceFormulaHolds}(G, A, c) \iff \operatorname{ValidSourceProof}(G, A, c).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Provenance/AcyclicSourceFormulaCorrectness.source_formula_iff_valid_source_proof` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source proof graph extends the existing finite acyclic rank carrier. Each conclusion has an optional direct source and finitely many alternative rules whose premises carry incoming-edge certificates.

The Boolean semantics is constructed recursively along the inherited rank. A direct enabled source is one disjunct; each alternative rule is another disjunct whose premises form a conjunction.

ValidSourceProof is an independent inductive relation. Well-founded induction proves that the recursive formula holds exactly when a proof uses only the available sources.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Provenance/AcyclicSourceFormulaCorrectness.source_formula_iff_valid_source_proof`
- Dependency: [D5/S3/ConceptDynamics/Provenance/FiniteProofGraphSourceSemantics](FiniteProofGraphSourceSemantics.md)
