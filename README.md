# trureturing

**A scientific method for AI to discover truth and find its next question.**

[Vision · 愿景](docs/VISION.md) · [Start your journey](#start-your-journey) ·
[Truth and computation](#truth-and-computation) · [Spacetime](#toward-holographic-spacetime) ·
[Information escape](#information-escape) ·
[Examples](#three-places-to-look) · [First run](#first-run) ·
[Lean source](D5/) · [Read the book](https://the-omega-institute.github.io/trureturing-mdbook/) ·
[Contribute](#take-part) · [Licensing](#license-and-foundations)

trureturing develops a scientific methodology through which AI can propose
questions, test its own conjectures, discover the limits of its representations,
and return checked results to a growing library. We want Turing computation to
find direction in those results: to recognize what is missing and choose a
fruitful next investigation. Autonomous choice of research direction is an
ongoing research goal.

The name expresses **true · return · Turing**. Truth guides the search;
verified knowledge returns as a premise for the next inquiry; computation
explores the connections. We call the structure we seek the **geometry of
logical truth**: dependencies, invariants, distinctions and the boundaries of
what an observer can recover.

The project brings together philosophical inquiry, theory, experiments and
Lean 4 formalization. Its ambition is broad; each proof establishes its exact
statement under its declared assumptions. The [Chinese vision and research
guide](docs/VISION.md) connects these ideas to existing work and the research
program through 2027.

## Truth and computation

Our philosophical starting point is that **truth is discovered, not created
by the act of computing it**. In this view, **Dao (道), or God (神), names an
encompassing network of truths and their logical relations**, within which a
finite observer discovers connections. This is the project's metaphysical
orientation, not a theorem about the existence of God or the physical universe.

Computation still does essential work: constructing examples, exposing
counterexamples, searching for proofs and checking them. A verified proof
extends what the library can justify. Returning that result to the library
lets later inquiry begin from a firmer foundation. Neither this conviction
nor a growing proof library establishes that one program can enumerate or
decide every truth.

The repository makes part of this geometry precise. Its
[dependency topology](D5/S3/ConceptDynamics/DependencyTopology/AlexandrovDependencyTopology.lean)
uses reachability in a dependency graph to define open sets. Its
[recovery criterion](D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)
says that, on a nonempty state space, a target admits a recovery function from
an observation exactly when that target is constant on each observation
fiber. Here a fiber is the set of states giving the same observation; the
existence of a recovery function alone gives no algorithm or cost bound.
These are precise structures with which to investigate our guiding picture.

## Start your journey

Bring a question that matters to you. In an installed **Claude Code or Codex**
with a local workspace and Git, paste this one sentence:

```text
Help me explore https://github.com/the-omega-institute/trureturing: use an existing checkout or clone it into a new directory if needed, read AGENTS.md and README.md, then read the relevant SKILL.md under skills/ to investigate a question I care about and find a checked result or a clearly stated open question.
```

The [agent and skills guide](docs/CONTRIBUTING.md#use-claude-code-or-codex)
explains how to begin with either client and turn an exploration into a
contribution.

This homepage is the tip of an iceberg. The examples offer a glimpse; the
larger shape is yours to explore, following definitions, assumptions and
connections with your own questions. What you find can change how you look.
An epigraph for that exploration:

> And if thou gaze long into an abyss, the abyss will also gaze into thee.

— Friedrich Nietzsche, *Beyond Good and Evil*,
[§146](https://www.gutenberg.org/files/4363/4363-h/4363-h.htm).

## From questions to knowledge

Ask a precise question. Use computation and tests to distinguish hypotheses.
Look for a proof, a counterexample, or the information still missing. Keep the
checked result with its assumptions, and make the unanswered question explicit.
People and AI can contribute; what others can reuse is the checked artifact.

> The last line of the ledger is always the first line of the next round.

A proof becomes a premise for further work. A refutation closes off a mistaken
route. A limit on what observations reveal tells us what to ask or measure next.
The purpose is to let understanding accumulate without losing its foundations:
each inquiry starts with what the last one actually established.

Today, the library contains Lean 4 proofs, research inputs, experiments and
tools for checking and recording results. Golden integers, Fibonacci weights
and Zeckendorf representations are one research thread; the examples below
also reach into conjecture refutation and the limits of local observations.
The ambition is to make more of this discovery process automatic. Each round
should state what would support or overturn its conjecture before the test,
reuse existing results, and seek a distinction its present representation
misses. A new observation, a better formulation or a counterexample can then
guide the next round. Applying this discipline to AI research is a method to
evaluate, not a guarantee of discovery.

## Toward holographic spacetime

We aim to study time and space together in a **holographic spacetime geometry**:
how a whole relational structure is represented through observations, and
under which conditions those observations support reconstruction and action.
This is a research program, with explicit models and open bridges to physics.

[Contextual spacetime arithmetic](docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md)
keeps finite event archives with time, position, causal order and provenance,
then studies what survives a numerical projection.
[Recursive relational observation](docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)
asks when observations preserve composition, shared sources and the target
of a question. The
[context geometry volume](docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)
develops distances using allowed experiments and their responses. These
volumes are theory inputs; their prose does not certify formal coverage.

A concrete [Lean counterexample](D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.lean)
shows why the distinction matters: in its finite archive model, adding an
inactive event can leave the current spatial readout unchanged while making
a specified temporal composition illegal. What a snapshot preserves and what
a history permits must therefore be checked separately in this model.

The holographic direction asks which additional relations make reconstruction
possible, at what resolution, and with what error and resource bounds.
Identifying these models with physical spacetime, or deriving a physical
holographic duality, remains outside the established results presented here.

## Research through 2027

The program continues through 2027 along three connected directions: scientific
methods for AI to choose and test questions; the geometry of proof dependencies
and observation limits; and spacetime models that retain the relations needed
for reconstruction and lawful composition.

The [research roadmap](docs/VISION.md#roadmap-2027) gives review periods and
concrete evidence for progress. Updates should follow new proofs,
counterexamples and reproducible experiments, revising explanations when the
evidence changes. The dates organize continued inquiry; they do not promise
a completed autonomous scientist or a finished physical theory.

## Information escape

We are developing an **information-escape judge** around four questions:

- **Where did information escape?** Name the objects, assumptions and
  observations under which distinct states remain indistinguishable.
- **How is that escape addressed?** Describe the added readout or relation,
  and show how a proof connects it to those objects and assumptions.
- **What new information emerges?** Identify the distinction now justified
  by the result and its verified connection to the readout.
- **Where does information continue to escape?** Exhibit a remaining
  indistinguishable pair, prove none remain within the stated scope, or mark
  the boundary open.

A **readout** is a way of observing a state; several readouts can observe
the same states. Fix one current catalog of registered theorem occurrences
and one shared state space, then remove just one occurrence. Pairs of distinct
states that the full catalog distinguished but the remaining readouts cannot
distinguish are that occurrence's **unique captures**. The
[EscapePairs definitions and proofs](D5/S3/ConceptDynamics/InformationEscape/EscapePairs.lean)
formalize this comparison.

For a **finite arena with at least two states**,
[StructuralNovelty](D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.lean)
connects a strict reduction in indistinguishability to a strict decrease in
the escape rate: the fraction of ordered distinct-state pairs left
indistinguishable. A unique capture witnesses that reduction. Zero unique
capture does not mean worthlessness: another occurrence can carry the same
distinction. Information here is contextual; this supplies neither a universal
value score nor a historical novelty judgment.

The judge is **under development**. Its current **declared-template findings
are Observe warnings and do not block admission**, as specified in
[A5.5 of the repository specification](docs/develop/spec/golden-ledger-repo-spec.md)
and implemented in the
[rule source](tools/StrataLint.Engine/Rules/TheoryGeneration/DeclaredTemplateBindingRule.cs).
Other admission checks retain their own effects. The rule's delta selection
determines which modules to inspect; it is separate from the mathematical
comparison within one current catalog above. The wider design is described
in the [Normative Draft](docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md);
its proposed system is not a claim of completed implementation.

Bring your own question to the [journey route](#start-your-journey), and use
these four questions to follow what becomes distinguishable and what stays open.

## Three places to look

**01 · Refute a conjecture.**
For positive n, let a(n) be the greatest integer k with `(1 + 1/n)^k ≤ 2`.
Greathouse's conjectured formula for OEIS A175406 was
`a(n) = floor((n + 1/2) log 2)`. At `n = 1121626023352383`, the formula gives
`777451915729368`, while the actual value is one less.
The [Lean refutation](D5/S0/Certificates/GreathouseLogTwoFloorRefutation.lean)
establishes `result : ¬ claim` using certified bounds on logarithms.
This refutes the literal universal formula; neither minimality of the witness
nor priority is claimed. [Problem and sources](Problems/oeis-a175406-log-two-floor-refutation.md) ·
[Explanation](Blueprint/D5/S0/Certificates/GreathouseLogTwoFloorRefutation.md).

**02 · Find what observations cannot tell you.**
Can knowing each part of a quantum system determine the whole? The
[local-marginal theorem](D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.lean)
constructs two distinct two-qubit states: a pure Bell state and the equal
classical mixture of `00` and `11`. Both have exactly the same reduced state
on each qubit. Even these complete local descriptions cannot identify the
joint state.

For finite factor dimensions `m, n ≥ 1` with `m × n > 1`, the theorem also
proves that the correlation sector in the Hermitian tensor model is orthogonal
to the local sectors and has real dimension `(m² − 1)(n² − 1)`. This identifies
precisely which directions the local description omits.
[Explanation](Blueprint/D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.md).

**03 · Build a result that holds beyond the examples.**
Write a natural number as its unique sum of nonadjacent Fibonacci weights
`1, 2, 3, 5, 8, …`. Replace each occupied weight Fᵢ by φⁱ, where φ is the
golden ratio, and call the resulting real value β(n). How far does this
coordinate fail to preserve addition?

$$\beta(a)+\beta(b)-\beta(a+b)\in\lbrace-1,0,1\rbrace.$$

[`deficit_three_valued`](D5/S1/Deficit/DeficitThreeValued.lean) proves this for
all natural inputs. Its proof combines an integer certificate with bounds on
the conjugate coordinate. The discrepancy is also the signed count of the two
lowest repeated-carry rules during digit normalization: a reusable connection
between an arithmetic algorithm and an exact bound, however large the inputs.
[Definitions and carry-count theorem](D5/S1/Deficit/DeficitInteger.lean) ·
[Explanation](Blueprint/D5/S1/Deficit/DeficitThreeValued.md).

## What is proved, and what is open

[D5/](D5/) contains the formal development. [Theory prose](docs/develop/theory/)
supplies research input, and [experiments](Evidence/) supply observations within
their declared scope. Neither prose nor numerical agreement establishes a
Lean theorem. The C# harness checks repository rules, proof reports and frozen
state; independent review examines whether statements faithfully express the
intended mathematics. Admitted proofs are recorded in the
[frozen ledger](Golden/Frozen/state/), with precise Lean statements and their
assumptions and axiom dependencies as the formal basis for reuse.

```mermaid
flowchart TD
    accTitle: From inquiry to reusable knowledge and the next question
    accDescr: Ask a question, compute and test hypotheses, check a proof or refutation, and keep a reusable result. A dashed arrow leads to the next open question.
    Q([Ask a precise question]) --> T[Compute and test hypotheses]
    T --> P[Check a proof or refutation]
    P --> R[[Keep a reusable result]]
    R -.-> N{What remains open?}
    classDef foundation fill:#edf2f7,stroke:#475569,color:#172033
    classDef proved fill:#e2f3ec,stroke:#28745b,color:#133f32
    classDef frontier fill:#fff4d6,stroke:#95651b,color:#553a10,stroke-dasharray:5 4
    class Q,T foundation
    class P,R proved
    class N frontier
```

*A schematic of inquiry, not runtime behavior or dependency data.* In words:
question → computation and tests → checked proof or refutation → reusable
result → next open question. A question can remain unresolved at any stage;
tests alone do not establish a theorem. The dashed arrow and diamond mark the
open frontier, so color is not needed to read the distinction.

The [book](https://the-omega-institute.github.io/trureturing-mdbook/) is a
browsable, searchable projection of [Blueprint/](Blueprint/), published by
[trureturing-mdbook](https://github.com/the-omega-institute/trureturing-mdbook).
It explains the work; the formal source remains authoritative.

Two explicit boundaries live in [Hearts.lean](D5/X_Frontier/Hearts.lean):

- **O-5:** `o5_independence`, a zero-localization claim for the canonical golden
  Euler germ, has an unresolved proof body (`sorry`).
- **O-6:** `o6WeilPositivityStatement` defines a Weil-positivity proposition.
  Defining that proposition supplies no proof of it.

These are open research obligations, not established impossibility results.
This repository does **not** establish the Riemann hypothesis.

## First run

Install [elan](https://github.com/leanprover/elan#installation) and the
[.NET SDK](https://dotnet.microsoft.com/en-us/download), with `lake`
and `dotnet` on your `PATH`. You also need Git, Make and a Bash-compatible shell.
elan selects Lean from [lean-toolchain](lean-toolchain). Mathlib is declared in
[lakefile.toml](lakefile.toml), with resolved dependencies in
[lake-manifest.json](lake-manifest.json). Install the .NET SDK version specified
in [global.json](global.json); the installed SDK must match that file.

Clone the project, then build just the introductory module. The `make` entry
prepares a private Lean cache; the first run may download dependencies.

```sh
git clone https://github.com/the-omega-institute/trureturing.git
cd trureturing
make lean LEAN_TARGETS=D5.S0.Conventions.WDigits
```

The [WDigits module](D5/S0/Conventions/WDigits.lean) directly reuses
**Mathlib's Zeckendorf development** to encode and decode natural numbers.
From that same directory, run this temporary example:

```sh
example_dir="$(mktemp -d)"
cat > "$example_dir/First.lean" <<'LEAN'
import D5.S0.Conventions.WDigits
open D5.S0.Conventions

#eval wdigits 42
#eval ((wdigits 42).map Nat.fib).sum
#check decode_wdigits
LEAN
lake env lean "$example_dir/First.lean"
rm "$example_dir/First.lean"
rmdir "$example_dir"
```

The two evaluations print `[9, 6]` and `42`. The list contains **Fibonacci
indices**, so its weights are `F₉ = 34` and `F₆ = 8`; it is not a list of the
weights themselves. `#check` displays the general decoding theorem's type.
Evaluating 42 illustrates the encoding; the theorem covers every natural number.

[Read the explanation](Blueprint/D5/S0/Conventions/WDigits.md).
`make help` lists the repository's command entry points.

## Take part

Start with one of the examples above. Reproduce it, improve its explanation,
report a mismatch between prose and a statement, or explore a precise open
question. Contributions in English and Chinese are welcome.

The [contribution guide](docs/CONTRIBUTING.md) walks you through forks, isolated
worktrees, checks and pull requests to `dev`.
[Issues](https://github.com/the-omega-institute/trureturing/issues) are a place
to bring a concrete question or reproducible problem.

## License and foundations

The root [LICENSE](LICENSE) contains Apache-2.0. The repository's
[licensing specification](docs/develop/spec/golden-ledger-repo-spec.md#第八部治理)
assigns Apache-2.0 to repository-produced Lean code, CC-BY-4.0 to text, and CC0
to data. Third-party dependencies retain their upstream licenses and applicable
notices.

Built on
[Lean](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).
Classical results and upstream proofs remain credited to their sources.
