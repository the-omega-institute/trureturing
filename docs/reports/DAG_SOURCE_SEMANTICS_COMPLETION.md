# DAG source-semantics completion

## Authority boundary

This report records the second source-to-theorem audit for DAG-related project materials. It is interpretive documentation. The Lean declarations and their kernel reports are authoritative.

The first extraction established prerequisite closure, executable frontiers, strict dependency coordinates, finite readiness under a supplied linearization, frontier-extension closure, append-only birth stages, conservative direct-edge embeddings, dependency-cone aggregates, information refinement along paths, fiber-internal paths, cyclic realization projection, and well-founded recursive closure.

A second audit identified six independent mathematical claims that were still implicit in the reference materials.

## 1. Consequence closure and ancestor-descendant duality

For a source set `S`, define

\[
\operatorname{ConCl}(S)=\{v:\exists u\in S,\ u\leadsto v\}.
\]

It is the least successor-closed superset of `S`. A node lies in the prerequisite closure of a target set exactly when its consequence cone meets that target set. This identifies knowledge foundation and structural impact as dual reachability views.

```text
D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure.lean
```

## 2. Well-founded frontiers and deadlock certificates

Every nonempty pending set under a well-founded prerequisite relation contains a node with no pending prerequisite. Therefore its executable frontier over the completed complement is nonempty.

Conversely, a nonempty pending set with empty frontier certifies failure of well-foundedness. This is the abstract mathematical content behind the distinction between an unfinished acyclic dependency region and a cyclic deadlock.

```text
D5/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier.lean
```

## 3. Dependency-closed append-only filtrations

For an append-only family of predecessor-closed stages, every present node has a first stage. A direct prerequisite is born no later than its dependent. Under a strict staging discipline requiring a prerequisite at an earlier stage, birth time is strictly increasing along dependency edges.

```text
D5/S3/ConceptDynamics/DagCompletion/DependencyClosedFiltration.lean
```

## 4. Reachability projection invariance

Prerequisite and consequence closures depend only on reflexive-transitive reachability. Adding a direct edge already implied by an existing path leaves both closures unchanged.

Thus closure-level semantics belong to the thin reachability projection. Direct-edge presentations may still differ in path multiplicity, scheduling, or dominator behavior.

```text
D5/S3/ConceptDynamics/DagCompletion/ReachabilityProjectionInvariance.lean
```

## 5. Strong-component quotient

Mutual reachability is an equivalence relation. Quotienting an arbitrary directed relation by this relation produces a partial order of strong components, and strict component reachability has no cycle.

This is the canonical mathematical bridge from a cyclic realization or flow graph to a logical DAG:

\[
\boxed{
\text{directed graph}
\longrightarrow
\text{mutual-reachability quotient}
\longrightarrow
\text{partial order of components}.
}
\]

```text
D5/S3/ConceptDynamics/DagCompletion/StrongComponentQuotient.lean
```

## 6. Minimal finite support

For any monotone property of finite support sets, inclusion-minimality is equivalent to failure after deleting each selected element. Therefore every coordinate of a minimal support is essential.

The theorem is independent of a specific interpretation. It applies to premise supports, observation packages, certified dependency bases, and finite sufficient definition families whenever their sufficiency property is monotone under adding support.

```text
D5/S3/ConceptDynamics/DagCompletion/MinimalDependencySupport.lean
```

## Combined structure

The complete extraction now separates four levels:

\[
\boxed{
\begin{aligned}
\text{direct graph} &\to \text{paths, frontiers, and path-sensitive bottlenecks},\\
\text{reachability projection} &\to \text{closures and the strong-component order},\\
\text{layered history} &\to \text{birth stages and dependency-compatible time},\\
\text{readout labels} &\to \text{answerability growth and residual contraction}.
\end{aligned}}
\]

This separation prevents several category errors:

- a direct graph and its transitive closure carry different information;
- a cyclic realization graph becomes a DAG only after quotienting strong components;
- an append-only stage number is a dependency coordinate only under closure assumptions;
- a support is irredundant only after an explicit minimality theorem;
- repository-specific statuses, services, and release actions remain consumers of these structures rather than Base mathematical definitions.
