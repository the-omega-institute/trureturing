# Finite Branch Atlases

## Abstract

Exhaustive refutations of every branch in a finite covering atlas exclude all admissible candidates.

**Theorem 1.1 (Branchwise exhaustive refutation excludes every admissible candidate).**

$$(\forall b, \operatorname{branchEmptyCheck}(A, p, b) = true) \Rightarrow \neg \exists x, p(x) = true.$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteBranchAtlas.no_admissible_of_all_branch_checks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every candidate is assigned to at least one branch by a finite Boolean atlas.

For each branch, the finite exhaustion checker certifies that no candidate is simultaneously in that branch and admissible.

Coverage selects a branch for any alleged admissible candidate, and the corresponding branch certificate supplies the contradiction. This is the reusable logical shell for Hadamard classification, finite automata exclusion, and finite causal-polytope searches.

## References

- Truth anchor: `D5/S0/Certificates/FiniteBranchAtlas.no_admissible_of_all_branch_checks`
- Dependency: [D5/S0/Certificates/FiniteExhaustion](FiniteExhaustion.md)
