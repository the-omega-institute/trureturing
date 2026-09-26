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

In practice, returning a result means making it available as a premise. A
theorem states its dependencies so that others can reuse it; a counterexample
identifies where a route fails so that others can avoid the same mistake.
An AI's output can support further reasoning when it returns to shared
knowledge with inspectable objects, conditions and evidence.

[Fixed-point philosophy](develop/theory/FIXED_POINT_PHILOSOPHY.md) develops
this orientation within the project: use beauty and intuition to choose
questions, logic to test conclusions, and extensions that preserve verified
results. [GICT](develop/theory/GICT.md) provides research background on
coordinates, transformations and invariants. These are theoretical references.
“Beauty is a compass; logic is a ratchet” is a research discipline, not a
substitute for a particular proof.

## The shape of logical truth

We use geometry to ask questions about relations. Which conclusions connect?
What survives a change of representation? Which distinctions does an
observation merge? What missing relation prevents a question from being
answered? Existing work gives this picture several mathematical entry points.

| Entry point | Relation under study | Existing result and scope |
| --- | --- | --- |
| Proof dependencies | How a declaration connects to others through dependency paths | [Dependency Alexandrov topology](../D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.lean) constructs an upper-set topology from reachability. A node's reachable upper set is its smallest open neighborhood in this topology. This describes dependencies, not physical distance. |
| Observation and recovery | Which states share a reading, and whether that reading determines a target | The [target recovery criterion](../D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean), on a nonempty state space, says a target can be recovered exactly when states with the same reading have the same target value. Existence does not establish computability or a cost bound. |
| Local and joint information | Which correlations remain unknown after observing each part separately | The [local marginal correlation blind spot](../D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean) gives two distinct two-qubit states: a Bell pure state and the equal classical mixture of `00` and `11`. They have the same two single-qubit reduced states. This counterexample limits claims of recovering a joint state from local readings alone. |
| Space and history | Whether a current spatial reading preserves historical conditions needed for later operations | The [hidden archive temporal-domain counterexample](../D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.lean) adds an inactive event to a finite event model, preserving the current region, selection and spatial reading while changing whether a temporal composition is legal. It does not identify the model's time labels with physical time. |

The recovery criterion links both counterexamples. The two quantum states share local readings but differ as joint states; the two archives share
a spatial reading but differ on a temporal operation's legality. Recovering
either target requires readings that separate its witness pair. This condition
alone supplies no executable or efficient reconstruction. Relating these models to proof dependencies or physical spacetime still requires maps
and checks of the relations, operations and error bounds they preserve.

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
5. **Return results to the next inquiry.** Reuse known theorems, preserve new
   reusable content, and state the conditions still to be met. Let the next
   question begin from an explicit boundary.

A [quantum error model question](../Problems/eidesen-2025-nice-error-basis-non-normal-stabilizer.md)
asks whether a size relation can hold while stabilizers fail to remain closed
under conjugation. The
[Lean construction](../D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.lean)
gives a projective error model on a four-dimensional complex space: the group
has 16 elements, and the logical and stabilizer sets for a code subspace each
have four. Their sizes satisfy `4 × 4 = 16`, but conjugation can take a
stabilizer outside the set. This suggests a research move: identify
which structural relation a numerical condition leaves unresolved, then test
it directly.

The finite-record
[lookup copier](../D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.lean)
illustrates another limit. It achieves zero retrospective loss; when its
construction depends on the copied records, each fails the model's
nonanticipation condition. Prospective gain is an independent input, so zero
loss does not ensure positivity for every such function. This motivates
scrutiny of test provenance, without establishing a general law of machine
learning performance.

Applying these structures to AI research selection is a methodological transfer
that needs practical evaluation. On questions not used to construct an answer,
does the AI reduce a stated gap, discover a reusable connection, or recognize
and stop an unproductive route? Those capabilities require corresponding
experiments; formalizing a method does not establish them by itself.

## Studying time and space through holographic geometry

We aim to place time, space, provenance and observation in a shared relational
framework: how does a whole appear through finite viewpoints, and how can
those viewpoints support reconstruction? This is the project's **holographic
spacetime geometry research direction**.

Imagine viewing the same history through different windows. Each window has a
visible extent; some windows overlap. Events have an order, records have
shared sources, and joining another window requires conditions to hold. The
research task is to determine which windows and relations suffice to answer
a target question, which distinctions remain hidden, and how the answers
change with resolution or budget. The analogy suggests questions; explicit
models carry the conclusions.

Existing work offers several connected routes:

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

Bringing these routes together requires attention to **joint realization,
recoverability, executability and cost**. Whether local readings come from the
same object or from incompatible candidate worlds changes the gluing problem.
Recovering a target value and recovering a complete history also have different
success criteria. The Lean temporal-domain counterexample above supplies one
concrete test: preserving current spatial readings alone does not preserve
all historical admission conditions in that model.

Here, holography names a research direction concerning wholes and observations.
This guide establishes no physical holographic duality, area law or model of
the universe. Correspondences between discrete event times, logical dependency
depth and physical spacetime coordinates require their own definitions,
proofs and, where applicable, empirical tests.

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

| Direction | Question to advance | Evidence of progress |
| --- | --- | --- |
| Scientific methods for AI | Can AI use observation blind spots to choose useful questions, connect results and revise unsuccessful routes? | Experiments on tasks specified in advance, with comparison conditions and reproducible results; reusable proofs or counterexamples where mathematical claims are made. |
| Geometry of logical truth | Which maps connect proof dependencies, observation distinctions and recovery while preserving the relations needed by a target? | Explicit definitions and maps, proofs of the required preservation properties, and counterexamples locating missing conditions. |
| Relational spacetime | Which shared sources and historical relations support reconstruction and legal composition at a given resolution and cost? | Reconstruction, gluing, error and resource bounds in stated models; supported correspondences and clearly identified open bridges to physics. |

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
