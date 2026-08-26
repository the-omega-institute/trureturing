# DAG source-semantics finite-model replay

## Status

This report is a supplemental bounded counterexample search. It does not replace Lean elaboration, kernel checking, axiom inspection, or repository admission.

The replay completed successfully with no counterexample in the stated finite ranges.

## Enumerated models

The check exhaustively enumerated every irreflexive directed graph on one through four labeled vertices and tested:

- prerequisite-closure and consequence-closure intersection duality for every target subset and every vertex;
- antisymmetry of reachability after quotienting by mutual reachability;
- existence of a ready node in every nonempty pending subset of every acyclic graph;
- invariance of reflexive-transitive reachability after adding any already-reachable edge.

It also enumerated:

- all birth-rank assignments with ranks from zero through the carrier size, checking nonstrict and strict dependency-birth inequalities whenever their hypotheses held;
- every monotone Boolean property of support subsets on zero through three coordinates, checking equivalence between inclusion-minimality and single-deletion minimality.

Result:

```text
PASS. No counterexample found in the enumerated finite models.
```

## Interpretation boundary

The replay searches for small finite counterexamples to the statements represented in:

```text
D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure.lean
D5/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier.lean
D5/S3/ConceptDynamics/DagCompletion/DependencyClosedFiltration.lean
D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance.lean
D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient.lean
D5/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport.lean
```

The general proofs are the Lean declarations themselves. This replay is retained only as an adversarial finite witness search and regression receipt.
