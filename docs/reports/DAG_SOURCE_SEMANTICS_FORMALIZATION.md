# DAG source-semantics formalization map

## Status and authority

This report records how DAG-related claims from the project's existing reference materials were converted into abstract mathematics. It is not a truth source. The Lean declarations and their kernel reports are authoritative.

Reference inputs used for this extraction:

- `bedc_2026-05-17T081940Z.pdf`, especially its milestone and dependency-DAG use as proof planning;
- `GICT (3).md`, especially the claims that documents are projections of a DAG, classification supplies coordinates, and guarded layers separate well-founded construction from cyclic self-reference;
- `PZG_BEDC (3).md`, especially append-only truth layers, dependency grades, and logical-DAG versus flow-graph separation;
- `OBSERVER-QUANTUM.md`, especially knowledge as constancy on readout fibers;
- `Solenoid 定义与证明.txt` and `main_2026-05-15.pdf`, especially finite-stage readouts and inverse-limit hidden fibers.

Existing Base declarations were reused wherever they already carried the mathematical content. In particular, this contribution does not redeclare `Concept`, `Refines`, `defectRelation`, answerable-question algebras, target recovery, inverse-limit completion, conservative pullback, ledger stabilization, or fixed-point selection.

## Extracted mathematical package

### 1. Prerequisite closure

For a dependency relation `edge` and target set `S`, the prerequisite closure is

\[
\operatorname{PreCl}(S)
=
\{u:\exists v\in S,\ u\leadsto v\}.
\]

It is extensive, monotone, idempotent, predecessor-closed, and the least predecessor-closed superset of `S`.

Lean module:

```text
D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure.lean
```

### 2. Executable frontier

For completed nodes `C` and pending nodes `P`, the executable frontier is

\[
\operatorname{Frontier}(C,P)
=
\{v\in P:\forall u,\ u\to v\Rightarrow u\in C\}.
\]

It is monotone in completed knowledge and in the pending carrier. For a finite pending set equipped with a topological linear order, its minimum is ready over the complement. Adjoining a frontier batch to a predecessor-closed set preserves predecessor closure.

Lean modules:

```text
ExecutableFrontier.lean
FiniteReadyExistence.lean
FrontierExtensionClosure.lean
```

### 3. Strict dependency coordinates and document projection

A strict coordinate `r : V -> R` satisfies

\[
u\to v\Longrightarrow r(u)<r(v).
\]

Strict increase propagates along nonempty paths and excludes cycles. This is the pure mathematical core of projecting a DAG into a linear document order or causal clock.

Lean module:

```text
StrictDependencyCoordinate.lean
```

### 4. Birth stages in append-only filtrations

For a monotone family of node sets `F_n`, every eventually present node has a unique first stage

\[
b(v)=\min\{n:v\in F_n\}.
\]

The node is absent before `b(v)` and present at every later stage.

Lean module:

```text
BirthStageFiltration.lean
```

### 5. Conservative DAG embeddings

A conservative embedding is injective and preserves and reflects direct edges among old nodes. Such embeddings compose and preserve all old reachability paths.

Lean module:

```text
ConservativeDagEmbedding.lean
```

### 6. Dependency-cone aggregates

For labels in a complete lattice, define the prerequisite meet and join over the full ancestor cone. Along dependency reachability, the meet is antitone and the join is monotone:

\[
u\leadsto v
\Longrightarrow
\bigwedge\operatorname{Anc}(v)\le\bigwedge\operatorname{Anc}(u),
\qquad
\bigvee\operatorname{Anc}(u)\le\bigvee\operatorname{Anc}(v).
\]

This supplies the abstract law behind weakest-grade propagation and accumulated axiom or evidence closure without assuming any repository-specific grade semantics.

Lean module:

```text
DependencyAggregate.lean
```

### 7. Knowledge refinement along dependency paths

When every edge carries a `Refines` witness from prerequisite readout to dependent readout, factorization composes along the whole path. Consequently:

- answerable Boolean questions grow downstream;
- target defects shrink downstream;
- target-risk sets shrink downstream.

Lean module:

```text
KnowledgeAlongDependency.lean
```

### 8. Fiber-internal paths

If every edge remains inside one readout fiber, every finite path remains in that fiber. A pair with distinct readouts cannot be connected by such a path.

Lean module:

```text
FiberInternalPaths.lean
```

### 9. Cycles across two graph layers

Suppose a realization graph maps edge-monotonically into an antisymmetric logical order. Any pair of realization states mutually reachable through cycles has the same logical projection. If the projection is injective, mutual reachability already forces equality in the realization layer.

This formalizes the distinction between a logical DAG and a cyclic copy, flow, or implementation graph. Cycles may survive only inside one logical equivalence class.

Lean module:

```text
CycleCollapseProjection.lean
```

### 10. Well-founded recursive closure and the mu-nu boundary

For the local dependency equation

\[
v\in S
\Longleftrightarrow
v\in B\ \lor\ \exists u,\ u\to v\land u\in S,
\]

well-foundedness of the predecessor relation implies uniqueness of the solution. A one-node self-loop with empty seed admits both the empty and full solutions, giving a concrete fixed-point gap outside the well-founded regime.

Lean module:

```text
WellFoundedRecursiveClosure.lean
```

## Scope boundary

The following source-language claims were deliberately not promoted into Base truth:

- that a repository service, release process, paper workflow, or agent is itself a mathematical DAG object;
- that a module-import edge is automatically a full proof-term dependency edge;
- that a displayed document order is the unique linearization of a theorem graph;
- that a numerical grade used by an implementation necessarily satisfies the abstract meet or join law;
- that every finite acyclic relation comes with a canonical topological order without supplying or constructing one;
- that inverse-limit, observer, or solenoid interpretations are new results when the current Base already contains the corresponding abstract carriers.

The contribution therefore transfers reusable mathematics from the source materials into Base while preserving the boundary between reference interpretation and certified theorem.
