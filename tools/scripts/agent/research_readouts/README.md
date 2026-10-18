# Research readings

This is the input contract for `readouts.py`, subordinate to `CLAUDE.md` and the existing specification. It computes readings for `skills/autonomous-research/SKILL.md`; it does not judge mathematics, proof shape, admission or research value. Existing §3.2 evaluation and mathematical settlement supply the evidence. No value function f is registered by this contract, and no expected value or ordering is computed.

## Compiled declaration dependencies

For sharpness/boundary source screening, `compiled_dependencies.py` reads an explicitly finite module domain at a fixed commit. Provide this JSON on stdin:

```json
{
  "revision": "<full HEAD commit SHA>",
  "domain": {
    "modules": ["D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.ParetoWeakPreorder", "D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.QuotientParetoWeakOrder"],
    "complete": true
  },
  "targets": ["D5.S3.ConceptDynamics.DefinitionEscape.Adjudication.pareto_weak_reflexive_transitive"]
}
```

Run `make -s -C tools compiled-dependencies < request.json`. The command builds only the reader, named modules and their compiler dependencies through `make lean`, including its existing cache ensure and reader lock. Lake owns incremental compiler reuse; there is no dependency-result cache, standing database, ledger or program-byte reuse key. Runtime data is temporary and removed when the command exits. The supported environment is the repository's pinned Lean/Lake toolchain, Git, make, .NET SDK and Python 3 on a platform supported by the existing cache entry. The entry resolves the repository from its own path and accepts invocation from other working directories.

The input has exactly the three displayed fields; module and target lists must be nonempty and duplicate-free. `domain.complete` is the caller's assertion that the list is its entire intended user population. It does **not** assert that the list covers all D5, or all reverse dependencies. If that population is not known, use `false`. The returned `domain` must accompany any reading. Unknown targets, unreadable modules, missing required values, a caller-incomplete population, a different/changing HEAD or modified Lean/Lake source inputs prevent a complete result. No incomplete result supplies an exact external user count. Successful acquisition from a clean fixed revision is required for exit 0; incomplete results exit 2 with named gaps and observed partial data.

`DEPENDENCY_NO_BUILD=1` skips compiler/cache acquisition and reads available artifacts. It always reports `freshness_unverified` or a named acquisition failure and exits 2; it cannot certify artifact freshness or an exact zero. Missing reader/stamp files report `missing_artifacts`, failed builds report `build_failed` with their exit code, and compiler read failures retain their original `raw.*` detail, including missing `.olean.server` / `.olean.private` parts. The default build path can repair missing artifacts; a failed repair remains an acquisition failure, separate from an empty source selection.

The `compiled-dependencies-v1` output contains every declaration in each successfully read domain module, with its compiler name, user name, owner, kind, private/internal flags and two edge records. `type` contains constants in the compiled type **and constructor names for an inductive**. `value` contains constants in the raw proof/definition value, using `CompiledAxioms.declarationDependencyParts`; `none` is `status: no_value` and `forward: null`, whereas `some []` has an observed empty direct list. Theorems, definitions and opaques missing a value produce `MISSING_REQUIRED_VALUE`. Axioms, inductives, constructors and recursors can legitimately have no value. Module `imports` are separate edges, associated with declarations by their owner module.

Each edge record has `forward` (what the declaration/module references) and `reverse` (which domain declarations/modules reference it), each with `direct` and `transitive` lists. Direct means one constant occurrence edge or one import edge; transitive includes direct edges and all positive-length paths of the **same kind**, excluding the starting node. Type and value paths are never mixed. Intermediate declarations/modules must belong to the explicit domain; outgoing constants/imports outside it are terminal boundaries. `boundary_constants` names the unexpanded constants. A complete result is exact only for these restricted paths, and makes no claim about paths that leave and then reenter the domain. Include additional modules and rebuild when such paths matter.

For each requested target, `external_value_users` selects public non-internal theorem/definition/opaque declarations in other domain modules with a raw value path to it; `value_paths` supplies one shortest witness per selected user. Private declarations and Lean internal-detail implementation constants remain graph vertices, and are excluded from this user list. User counts are distinct declaration identities, never a sum of intermediates or paths. Compiler kinds and Lean's `Name.isInternalDetail` determine this filter; these flags do not authenticate author intent or source-level relevance. Inspect the named users before treating them as research sources.

**Raw expression occurrence is not a live path after reduction and dead-term removal under `CLAUDE.md` §3.2.** It establishes neither indispensability, an escape witness nor research value. Imports and type references supply no proof-use evidence. This command is a source-screening readout, not a proof-shape or admission judge; the existing §3.2/§3.3 evaluation remains responsible for those conclusions. No whole-D5 ranking or historical selection conclusion follows from a finite query.

`make -C tools compiled-dependencies-test` runs the protocol and graph tests without Lean preparation. `make ci-unit UNIT=tests-lean` also exercises the production `compiled-dependencies` make entry, its normal Python acquisition and the built `dependencyReadout` executable on the existing compiler fixtures. Its private core-only native project needs the pinned toolchain and the built .NET producer, and starts without the executable or a project cache. It checks JSON value users, type/import-only non-users and named unknown declarations from a path containing spaces and a different working directory. `make compiled-judge-test` runs the real public/server/private compiler fixtures through the existing compiled-judge test program, including import-only/type-only/value/helper cases, inductive constructor edges and absent versus empty values.

## Carrier and acquisition

One unit is one existing preregistration issue in `the-omega-institute/trureturing`. Before substantive execution, append one **unchanged issue comment** containing a fenced `research-prereg-v1` JSON block. Its GitHub REST `created_at` is the registration time of every prediction in that block. The program requires `updated_at == created_at`. The timestamp is obtained from GitHub metadata, never a payload field that would need an edit after creation. Do not put the block in the issue body: an issue's `updated_at` also reflects activity unrelated to body edits.

Append an unchanged comment containing one fenced `research-terminal-v1` JSON block to report the current settlement or obstacle. A batch has at most one block of each kind per issue, across the issue body and all comments. To revise an event, threshold or predictions, preregister a fresh unit before execution; do not replace the old blocks. Seat independence and the fidelity of the source judgment remain obligations of the owning research workflow.

Read live carriers and cited evidence with:

```sh
make -s -C tools research-readouts ISSUES="123 456" AS_OF="<UTC cutoff>"
```

`ISSUES` lists existing issue numbers; `AS_OF` is required. The command uses read-only `gh api` requests for issue bodies, **all comment pages** (`--paginate --slurp`), and cited issue/PR bodies or issue comments. Citation URLs must resolve to their own returned `html_url`. Network, permission and pagination-shape failures are named failures, never empty queues.

For offline replay, omit `ISSUES` and provide a JSON snapshot on stdin:

```sh
make -s -C tools research-readouts AS_OF="<UTC cutoff>" < /external/path/snapshots.json
```

The snapshot has exactly `issues` and `evidence`. `issues` is an array of objects with exactly `issue` (the REST issue object) and `comments` (the complete flattened REST comment array). `evidence` is an array of cited REST issue/PR/comment objects not already included in `issues`. Raw REST objects retain at least `html_url`, `body`, `created_at`, `updated_at`; extra API members are ignored. Conflicting copies of the same source and duplicate unit identities fail. Snapshots are supplied evidence: offline mode cannot authenticate GitHub metadata or detect omitted comments. Acquire complete snapshots from GitHub for attributable readings. Do not commit snapshots or aggregates to the main repository.

## Preregistration block

Use a code fence whose opening line is exactly `` ```research-prereg-v1 ``. Its JSON object has exactly these fields:

| Field | Contract |
| --- | --- |
| `event` | Object with exactly nonempty `statement` and `quantifiers` strings. The binary event is the truth of this fully quantified statement, under its stated assumptions. |
| `deadline` | UTC cutoff, strictly after the carrier's creation time. |
| `scoring_rule` | Exactly `{"name":"binary-brier","version":1}`. Version is an integer. |
| `surprise_threshold` | Finite JSON number in [0,1], chosen for this preregistration. There is no tool default. |
| `predictions` | Array of independent-seat predictions; `[]` explicitly records that predictions were not obtained. |

Each prediction has exactly:

| Field | Contract |
| --- | --- |
| `seat` | Nonempty unique seat identity in this unit. |
| `model_family` | Nonempty attributable model-family label; the output preserves actual diversity, without assuming different seats imply different families. |
| `event` | Exactly the same statement and quantifiers as the unit's event. |
| `probability` | Finite JSON number in [0,1] predicting that the event is true. Booleans, strings, null, NaN, infinity and out-of-range numbers fail. No clamp or coercion. |

All timestamps use UTC `YYYY-MM-DDTHH:MM:SSZ`. JSON duplicate keys, unknown or missing block fields, unsupported versions and malformed research fences fail. Event matching is exact text equality, not an equivalence proof. The owning evaluator must check the quantified statement's fidelity; a matching label alone is insufficient.

## Terminal block and evidence

Use a code fence whose opening line is exactly `` ```research-terminal-v1 ``. Its JSON object has exactly:

| Field | Contract |
| --- | --- |
| `event` | Exactly the preregistered statement and quantifiers. |
| `execution_started_at` | Recorded substantive execution start. It must be at or after registration, before the deadline, and no later than terminal publication. Registration later than this start fails `POSTHOC_PREDICTION`. |
| `status` | `proved`, `refuted`, `invalid` or `unresolved`, taken from the owning route's current evidence. Only proved/refuted supply a binary answer. |
| `settled_at` | Recorded mathematical settlement time for proved/refuted; null for invalid/unresolved attempts. It must lie between execution start and terminal publication. |
| `evidence` | Reference to existing settlement or obstacle evidence, with exactly `url` and a nonempty verbatim `excerpt`. |
| `shape_evidence` | Reference with exactly `url` and `excerpt`, or null when no settled §3.2 judgment was obtained. A supplied excerpt must be exactly `proof_shape: content` or `proof_shape: bind-only` from the unit's existing live-path evaluation. Invalid/unresolved attempts require null. |

References resolve to this repository's issue/PR bodies or issue comments. Each excerpt must occur in the resolved source body. `shape_evidence` reads x=1 for the existing content judgment and x=0 for bind-only. A missing judgment leaves x unmeasured for a settled answer. The program verifies reference identity and excerpt presence; it does not certify that the cited evaluator correctly assessed the live proof path or that the settlement proves/refutes the exact event. Apply the existing independent evaluation, Lean and admission requirements before supplying those judgments. The recorded execution/settlement times are workflow assertions, not independently observed process telemetry.

A scored settlement must occur **by the registered deadline**, according to its recorded `settled_at` and cited existing evidence. The reporting comment may be published later: reporting time is distinct from mathematical settlement time and from preregistration time. A late report cannot supply a late prediction, alter the registered event or replace missing settlement evidence; the owning evaluator checks the recorded settlement time against that evidence. The `AS_OF` snapshot must reach every included carrier's `updated_at`; future or incoherent metadata fails. An already settled answer can be scored before its deadline. An unresolved unit requires `AS_OF` to reach its deadline before claiming z=1; otherwise the batch fails `BEFORE_DEADLINE`. An absent terminal, invalid attempt or late settlement leaves the mathematical answer unresolved at the cutoff. It supplies no negative answer and no Brier score.

Missing whole preregistrations (historical issues) and explicit empty prediction arrays yield named unscorable readings. They never create y or a mode, and no historical probability is filled in. Without a preregistration, `evidence_status` is `missing-preregistration`: a terminal cannot be matched to a registered event. Present terminal blocks still require valid fields, timestamps and resolved references, even without a preregistration or a timely answer. Missing mandatory fields in a present block fail the batch. A missing terminal after the deadline has structural z=1; it does not assert why research was unfinished.

## Deterministic output

The command writes a single JSON object to stdout, without persistent state or a cache. Invalid input exits 2 with `READOUT <named failure>` on stderr and **no partial stdout**. The canonical test command is `make -C tools research-readouts-test`; the existing `tests-workflow-script` CI unit runs it through `ResearchReadoutsScriptTests`. Its whitelist covers this directory and `skills/autonomous-research/*`.

Probabilities and scores are computed as exact rational numbers from JSON decimals. Output rationals are reduced strings (`"0"`, `"1"`, `"1/16"`); no floating-point rounding occurs. Units and seats are sorted by their identities. For a settled binary answer a, each seat's binary Brier loss is `(p-a)^2` (version 1, without the two-category factor of two). The aggregate prediction is the equally weighted arithmetic mean of seat probabilities. `surprise` is the **mean of seat Brier losses**, not the Brier loss of the aggregate prediction. y=1 iff this mean is at least the registered threshold. Proper scoring measures prediction error; neither the score nor its threshold measures mathematical information or research value. No family weighting or calibration claim is made.

Each unit reports its issue, event, metadata-derived registration time, seat/family scores, aggregate probability, surprise, x/y/z, mode, score status and evidence status. A settled unit without predictions has y=null and mode=null. With predictions but no timely answer, z=1 and x=y=0 are **structural zeros** required by xz=yz=0; scores stay empty and surprise stays null. They are not observations that the answer was expected. With predictions and an answer but no shape judgment, scoring proceeds, x and mode stay null. Illegal nonbinary coordinates or nonzero xz/yz are rejected by the classifier; supplied x/y/z fields are not accepted as substitutes for evidence.

The five modes are:

| Mode | (x,y,z) |
| --- | --- |
| `p0` | (0,0,0) |
| `p2` | (1,0,0) |
| `p5` | (0,1,0) |
| `p25` | (1,1,0) |
| `p3` | (0,0,1) |

The batch always reports all five `five_counts`, total units, scored units, `mode_denominator`, `score_coverage`, `mode_coverage` and `missing_counts`. Counts of prediction, answer, shape and mode missingness can overlap. `score_coverage` is scored units / all units; unresolved and missing-prediction units are excluded from answer scoring. `mode_denominator` includes only complete modes; X=(p2+p25)/denominator, Y=(p5+p25)/denominator and Z=p3/denominator describe that subset, not the excluded units. Zero denominators produce null rates, never invented zeros. Complete five-cell counts are retained even when X/Y/Z coincide: the count difference (1,−1,−1,1,0) preserves these rates but changes the joint distribution. No f, E[f], ranking, residual-sufficiency judgment, quota or admission decision is produced.
