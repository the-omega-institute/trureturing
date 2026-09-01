# LRAT Refutations and Unsatisfiability

## Abstract

Mathlib LRAT empty-clause proofs are exposed as exact propositional unsatisfiability certificates.

**Theorem 1.1 (Empty-clause derivability is equivalent to unsatisfiability).**

Lean statement: `D5/S0/Certificates/LRATUnsatisfiable.empty_clause_proof_iff_unsatisfiable`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/LRATUnsatisfiable.empty_clause_proof_iff_unsatisfiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib's lrat_proof command constructs kernel-checked proof terms in the Sat.Fmla.proof semantics.

For the empty clause, that proof target reduces exactly to the assertion that every valuation satisfying the input formula yields false.

The repository wrapper therefore adds no second checker. It gives later SAT-backed open-problem lanes one named soundness boundary for imported LRAT certificates.

## References

- Truth anchor: `D5/S0/Certificates/LRATUnsatisfiable.empty_clause_proof_iff_unsatisfiable`
