# trureturing

**A scientific method for AI to discover truth and find its next question.**

[Vision](docs/VISION.md) · [Start your journey](#start-your-journey) ·
[Truth and computation](#truth-and-computation) · [Examples](#three-places-to-look) ·
[Spacetime](#toward-holographic-spacetime) · [Information escape](#information-escape) ·
[First run](#first-run) ·
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
statement under its declared assumptions. The [vision and research
guide](docs/VISION.md) connects these ideas to existing work and open research
directions.

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

Choose questions whose answers could supply missing premises, expose overlooked
distinctions or connect existing results. Search existing proofs and literature;
state what would support or overturn a route, then design tests that distinguish
alternatives. Keep reusable results with their assumptions.

> The last line of the ledger is always the first line of the next round.

A proof supplies a premise; a counterexample refutes a claim within its stated
scope. An observation limit can suggest what to measure next. When progress
stalls, check whether the representation misses a needed distinction.
Evaluate this proposed method on withheld questions, against a stated baseline
with matched information and resources.

The library contains Lean 4 proofs, theory inputs, experiments and checking
tools. Golden integers, Fibonacci weights and Zeckendorf representations are
one thread; the examples below also explore conjecture refutation and limits
of local observation.

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

## Toward holographic spacetime

We study **holographic spacetime geometry** as a question about time, space and
observation: when do partial records support reconstruction and action?

Theory inputs study
[event archives](docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md)
retaining time, position, causal order and provenance;
[when observations preserve](docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)
composition, shared sources and targets; and
[experimental distances](docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)
defined through allowed experiments and responses. Their prose does not certify
formal coverage.

A [finite-archive counterexample](D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.lean)
leaves the current spatial readout unchanged when an inactive event is added,
while making a specified temporal composition illegal.

A positive [tree extension theorem](D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean)
applies to nonempty local record sets on a finite tree: each recorded variable
must occur on a connected subtree, and neighbors must allow exactly the same
joint assignments on their full overlap. Then any allowed local record extends
to a record on the union of the local variable sets, satisfying every local
constraint.

This establishes a compatible completion; uniqueness, original-history recovery
and computational cost require further results. Reconstruction with stated
resolution and error bounds, and links to physical spacetime or holographic
duality, remain research questions.

## A continuing research program

The [research directions](docs/VISION.md#research-directions) ask:

- Can AI choose questions that yield reusable knowledge?
- Which maps connect proof dependencies and observational distinctions?
- Which historical relations support reconstruction and legal composition?

The guide states what would advance each question.

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

## What is proved, and what is open

Mathematical reuse rests on the statements, checked proof terms and axiom
dependencies in the [Lean source](D5/). The
[frozen ledger](Golden/Frozen/state/) tracks frozen module identities.
[Theory prose](docs/develop/theory/) supplies research input, and
[experiments](Evidence/) supply observations within their declared scope;
neither substitutes for a Lean proof. The C# harness checks repository rules,
proof reports and frozen state. Independent review examines whether statements
faithfully express the intended mathematics.

```mermaid
flowchart TD
    accTitle: From inquiry to reusable knowledge and the next question
    accDescr: Ask a question, test hypotheses, check a proof or refutation, and keep a reusable result. Dashed paths return unresolved questions from testing, proof checking or results to the next inquiry.
    Q([Ask a precise question]) --> T[Compute and test hypotheses]
    T --> P[Check a proof or refutation]
    P --> R[[Keep a reusable result]]
    R -.-> N{What remains open?}
    T -.-> N
    P -.-> N
    N -.-> Q
    classDef foundation fill:#edf2f7,stroke:#475569,color:#172033
    classDef proved fill:#e2f3ec,stroke:#28745b,color:#133f32
    classDef frontier fill:#fff4d6,stroke:#95651b,color:#553a10,stroke-dasharray:5 4
    class Q,T foundation
    class P,R proved
    class N frontier
```

*A schematic of inquiry, not runtime behavior or dependency data.* Questions
can remain unresolved, and tests alone do not establish a theorem. Dashed
paths return remaining questions to another inquiry, including when no checked
result was obtained. Labels and shapes carry the distinction without relying
on color.

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
