# trureturing: finding direction in truth

[Project overview](../README.md) · [Contribute](CONTRIBUTING.md) ·
[Theory inputs](develop/theory/) · [Formal source](../D5/) ·
[Research directions](#research-directions)

**The project's core is a scientific methodology through which AI can make
its own discoveries, explore the geometry of logical truth, and give Turing
computation a direction informed by existing knowledge and unresolved gaps.**

Here, discovery includes finding new relations, recognizing the blind spots of
one's own representations, and revising the methods used to investigate them.
We want AI to formulate questions, search the literature and existing proofs,
design tests that distinguish explanations, accept counterexamples, and return
checked results to a shared network of knowledge. How to sustain the choice of
valuable research questions remains a goal to investigate and evaluate.

This guide sets out the project's vision, connects it to existing research,
and identifies open directions. It complements the
[repository specification](develop/spec/golden-ledger-repo-spec.md); theory
volumes and research plans do not acquire the status of formal proofs by
appearing here.

## Truth, return and Turing computation

**true · return · Turing** expresses three connected intentions: seek truth,
return verified knowledge as a premise for further reasoning, and let
computation find direction through those connections.

Our philosophical position is that truth is not created by an act of
computation. Computation enables finite observers to discover, express and
verify relations within it. From this perspective, Dao (道), or God (神), can
name an encompassing network of all truths and their logical relations.
Each proof and each refuted conjecture changes our knowledge of that network.

This position proves nothing about the existence or nature of Dao, God or the
universe. It supplies no algorithm enumerating or deciding every truth.
Computation still constructs counterexamples, searches for proofs and checks
them. What truth is and how its proofs are obtained remain different questions.

Return a result to shared knowledge for reuse as a premise, with inspectable
objects, conditions and evidence. A
theorem can be reused where its assumptions hold; a counterexample refutes a
claim within its stated scope and can suggest which conditions to investigate next.

[Fixed-point philosophy](develop/theory/FIXED_POINT_PHILOSOPHY.md) outlines
a discipline: beauty and intuition guide questions, logic tests
conclusions, and extensions preserve verified results.
[GICT](develop/theory/GICT.md) studies coordinates, transformations and
invariants. [Math Myth Match](develop/theory/MATH_MYTH_MATCH.md) compares
philosophical traditions through questions about observation, shared origins
and what expressions refer to, preserving differences. These volumes
are research inputs; their guiding metaphors do not substitute for proofs.

## The shape of logical truth

We use geometry to ask questions about relations. Which conclusions connect?
What survives a change of representation? Which distinctions does an
observation merge? What missing relation prevents a question from being
answered? Existing work gives this picture several mathematical entry points.

- **Proof dependencies.** How does a declaration connect to others through dependency
  paths?

  [Dependency Alexandrov topology](../D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.lean)
  constructs an upper-set topology from reachability. A node's reachable upper set is
  its smallest open neighborhood in this topology. This describes dependencies, not
  physical distance.

- **Local and joint information.** Which correlations remain unknown after observing
  each part separately?

  The [local marginal correlation blind spot](../D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean) gives two
  distinct two-qubit states: a Bell pure state and the equal classical mixture of `00`
  and `11`. They have the same two single-qubit reduced states. A
  [joint expectation](../README.md#02--find-what-observations-cannot-tell-you) separates this pair without
  establishing recovery of arbitrary joint states.

- **Space and history.** Does a current spatial reading preserve the historical
  conditions needed for later operations?

  The [hidden archive temporal-domain counterexample](../D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.lean)
  adds an inactive event to a finite event model, preserving the current region,
  selection and spatial reading while changing whether a temporal composition is legal.
  It does not identify the model's time labels with physical time.

Both counterexamples hide different target values behind equal readings.
Separating one pair need not make recovery possible.
[Recovery](../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)
requires that **any two states with the same reading have the same target value**.
On a nonempty state space, this condition ensures a recovery function exists
but supplies no algorithm or cost bound.
Connections to proof dependencies or physical spacetime require maps and checks
of the relations, operations and error bounds they preserve.

For further reading,
[proof topology, involutive logic and observational escape](develop/theory/PROOF_TOPOLOGY_DIAGONAL_ESCAPE_THEORY.md)
examines connections between dependency topology and observation kernels.
[Definition escape spectrum completion](develop/theory/DEFINITION_ESCAPE_SPECTRUM_COMPLETION.md)
studies residual blind spots under a given language and budget. Formal
coverage must be checked against the relevant Lean declarations, claim by
claim; a related link does not establish that an entire volume is formalized.

## How AI can find its next direction

The method links five steps:

1. **Work backward from the target to the gap.** Specify the objects, shared
   sources, allowed operations, question and resource limits. Check whether
   existing results supply the premises that are needed.
2. **State criteria before testing.** Specify which observations would support
   a proposed route and which counterexamples would overturn it. Search the
   literature for existing tools and alternative formulations.
3. **Look for distinctions the representation misses.** Seek two realizations
   with the same readings but different target answers or different legal
   operations. Failure to find a counterexample still leaves sufficiency to
   be proved.
4. **Let evidence guide the next step.** Use experiments to distinguish routes,
   and proofs or counterexamples to settle mathematical claims. When a
   representation cannot express a needed distinction, investigate new
   relations, languages or forms of observation.
5. **Return results to the next inquiry.** Reuse known theorems and preserve new
   reusable content. Show which conclusions supply needed premises, checking
   assumptions and identifying the remaining gaps.

A [circle theorem](../D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.lean)
rules out choosing a square root continuously around the whole complex unit circle.
It suggests a next question: how accurate can a constrained approximation be?
For any real `L ≥ 0`, a circle map stretching shortest-arc distances by at most
a factor of `L` has [uniform mean squared chord error](../D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.lean)
at least `2/(2L+1)`, measured between its squared output and the input.
For every `L ≥ 1/2`, a map attains this bound.

The finite-record
[lookup copier](../D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.lean)
achieves zero retrospective loss. If construction uses every copied record,
each fails the model's nonanticipation rule: tested records must be absent from
construction dependencies. Prospective gain is specified separately; zero loss
does not ensure positivity for every gain function. This motivates checking
test provenance, without establishing a general law of learning performance.

Evaluate AI research selection on questions withheld from method design.
Fix the baseline, matched information and resource budgets, and success and
stopping criteria before testing. Report evidence for each question's outcome:
premises supplied, distinctions exposed, routes ruled out, failures and
unresolved gaps. These experiments evaluate research selection; formalizing
the structures alone does not establish this capability.

## Studying time and space through holographic geometry

We aim to study time, space, provenance and observation through **holographic
spacetime geometry**: how does a whole appear through finite viewpoints, and
when do those viewpoints support reconstruction?

A [Boolean counterexample](../D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.lean)
uses three windows onto variables: one permits pairs with `x=y`, another
`y=z`, and the third `x≠z`. Their allowed records agree on every overlap:
either value of the shared variable is permitted. Yet no joint record
satisfies all three constraints. Finding relations that make local agreement
sufficient is the task; the tree criterion below gives one answer.

The [tree extension theorem](../D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean)
assumes nonempty local record sets on a finite tree: each recorded variable's
occurrences form a connected subtree, and neighbors allow exactly the same
joint assignments on their full overlap. Every allowed local record extends
across all recorded variables, satisfying every local constraint.
Do all completions of a fixed local record agree on the target value?
Additional global constraints can exclude every extension.
Unique completion, original-history recovery and computational cost require
further results.

Here, holography names a research direction concerning wholes and observations.
This guide establishes no physical holographic duality, area law or model of
the universe. Correspondences between discrete event times, logical dependency
depth and physical spacetime coordinates require their own definitions,
proofs and, where applicable, empirical tests.

Theory inputs explore several routes:

- [Contextual spacetime arithmetic](develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md)
  begins with finite event archives that retain time labels, positions, causal
  partial orders and provenance. It studies projections from these richer
  representations to arithmetic readings, asking which archive distinctions
  must still be preserved when numerical values coincide.
- [Recursive relational observation](develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)
  studies observation quotients, strict gluing and compatible completions.
  [Joint relations and clocks](develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_RELATIONS_CLOCKS.md)
  develops joint relations and temporal readings further.
- [Executable context geometry](develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)
  incorporates allowed experiments, failure outcomes, response differences and
  gain requirements.
  [Process geometry](develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)
  and [recovery geometry](develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)
  provide further research directions.
- The [quantum observation extension](develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)
  and [machine learning observation extension](develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md)
  explore correspondences between observation structures. Each transfer must
  check the specific conditions on quantum states, probability laws, training
  data and allowed operations.

## What can serve as the next premise

Declarations, proof terms and axiom dependencies in the
[Lean source](../D5/) are the project's mathematical source of truth. Theory
volumes propose concepts and routes. Experiments supply readings for stated
inputs and scales. The C# harness checks repository rules, reports and frozen
state. Independent review checks whether formal statements faithfully express
the intended claims.

This division leaves room for a broad philosophical orientation while keeping
each reusable conclusion precise. Unproved questions remain unresolved; a
failed proof attempt does not establish unprovability.
[O-5 and O-6](../D5/X_Frontier/Hearts.lean) still have open obligations, and
the project does not claim to have solved the Riemann hypothesis.

## Research directions

Research routes change as evidence reveals new connections and limits.
Three questions guide the next work:

- **Scientific methods for AI.** Can AI use observation blind spots to choose useful
  questions, connect results and revise unsuccessful routes?

  **Evidence of progress:** Experiments with tasks and comparisons specified in advance,
  reproducible results, and reusable proofs or counterexamples for mathematical claims.

- **Geometry of logical truth.** Which maps connect proof dependencies, observation
  distinctions and recovery while preserving the relations needed by a target?

  **Evidence of progress:** Explicit definitions and maps, proofs of the required
  preservation properties, and counterexamples locating missing conditions.

- **Relational spacetime.** Which shared sources and historical relations support
  reconstruction and legal composition at a given resolution and cost?

  **Evidence of progress:** Reconstruction, gluing, error and resource bounds in stated
  models; supported correspondences and clearly identified open bridges to physics.

When a theorem, counterexample or reproducible experiment changes a conclusion,
revise its explanation and the questions that follow from it. Keep these entry
documents compact by replacing weaker explanations, removing repetition and
linking to the detailed sources. Preserve the assumptions and boundaries needed
to use each result. Correct existing theory volumes through additions; Git
preserves history, while the entry documents present current understanding.

An update has a concrete test: can readers find the definitions, check the
stated results, see the remaining conditions, and use them to pose a better
next question?

Choose a verifiable task from the [contribution guide](CONTRIBUTING.md): improve
an explanation, reproduce a counterexample, connect existing results, or
advance a missing proof.
