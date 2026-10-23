# StrataLint trust topology

Production harness projects, scripts, manifests, and architecture material live under
`tools/`; all harness test and compile-fail projects live under `tools/tests/`.
`Meta/` is the data side of this boundary and contains no harness program directory.

CI is one workflow, `ci-current.yml`, which consumes the sole CI_UNITS selection and execution contract in
`Meta/ci-units.json`. Its `detect` job fetches commits and trees only, verifies the
event candidate through `ci-entry.sh` (the checked-out `GITHUB_SHA`, the complete
event range and the pull-request merge parents), lists the changed paths, and
`ci_detect.py` decides from the `CI_UNITS` sections in that contract which
units the change hits. A section is named by its job id; `[*]` patterns apply to
every unit; `*` also matches `/`, `?` matches one character and `!` excludes. Detection
validates and matches the complete changed-path list without a path-count
cutoff. The patterns are written, not derived from
project registrations, FILEMAP or call graphs.

Each test project, selftest, compile-fail proof, FILEMAP and current is one job
that runs only when hit. Selected current first runs its narrow source prerequisite
in the native source job; completed source rejection blocks the selected fan-out.
When current is unselected this phase is skipped. Independent selected jobs then
run in parallel; steps within a job may be serial. `ci-unit.yml` supplies the common checkout, candidate verification, .NET
and optional Lean cache steps; its unit id selects the declaration consumed by
`ci_checks.py`, which runs the canonical project/test-evidence or command implementation. The current job produces one Lean report and
runs `check-current`, Scribe, and (for pull requests) `check-delta` against the
first parent as data. The one required check is the `required` job:
`ci_required.py` is green only when detection succeeded, the unit sections and the
jobs it needs correspond one to one, every hit unit succeeded with its matching execution
identity and every missed unit was skipped. Each hosted entry removes remote state after the fixed candidate and any
required base data are available, and no job executes protected-base code; the
actual required check names and deployment state come from the installed ruleset
and real Actions runs.

Local `make gate BASE=<commit> [PURPOSE=pull-request|push]` and the local harness
entry consume the same contract and check implementation, including current subchecks,
complementary test filters, prerequisites and canonical TRX verification. Local changes
include the staged, unstaged and untracked candidate, deletions and both rename paths.
An invalid explicit base fails; an empty diff is distinct from unavailable hosted base.
`make gate-plan` reports selection, fixed base, actual candidate tree identity, contract
revision and purpose without claiming execution. Local remotes persist; hosted event
authentication, cache transport, publication and required results remain host obligations.
Delta exit 3 is observable protected-only early feedback on both adapters, with no
review authorization; other failures retain their exits. Each unit/current shares one
7200-second compute allowance across its phases, excluding preparation. The source
job charges judge compilation and source execution to current and exports only the
remaining allowance through ci_compute; the continuation cannot start a fresh budget.
Bootstrap/input failures remain distinct from completed source rejection, preserving
independently reachable report fallback. Required directly checks this prerequisite
as well as every selected unit. Ready report validators run source evidence, Scribe,
current, applicable delta and compiled audit before project publication; independent
semantic rejection does not revoke valid report publication eligibility.
`make test` remains the explicit lean-report plus check-current entry. A project-specific
test is run with `make -C tools test TEST_PROJECT=...`; local success is early
feedback and does not replace remote required checks.

`StrataLint.TestEvidence` owns `list-test-owner-assemblies`, `verify-trx`, and
`compile-proof`. It references only `StrataLint.Engineering` (registered identity/schema) and
`StrataLint.Runtime` (bounded execution and the hang protocol). Single-project
selection reads only `Meta/engineering-projects.json`; Engine retains complete
repository source, glob, namespace and topology admission. Solution runs retain
the registered owned-test assembly floor, waived only for filtered solution runs. `dotnet-test.sh` and the compile-proof make target
build and invoke this executable. CLI forwards the same commands through a project
reference. TRX validation requires successful executed tests, the selected owner
assemblies, and no infrastructure hang guard skips. Its owned tests run as their
own CI unit.

The report format identifier governs strict artifact acceptance. Native Lake facets own report reuse
and require selected Lean/audit targets and the current inspector build. Compiler traces, utility
inputs and the report format decide reuse; validators check structure and artifact integrity
without comparing stored source digests with current repository bytes. Reused rows retain their actual producer
origins. Native report artifacts travel with `.lake/build` in the project snapshot;
there is no separate report cache or preparation shortcut. Remote seed compatibility
remains the resolved mathlib revision, with OS/architecture binary isolation.
The current job builds the report once and transports it with the project build directory;
unit jobs consume their own results and do not select another report run.

No release command selects a CI run or report artifact. Truth-release bundles are
verified offline from their declared source and digest; eligibility and branch
protection remain separate observations. Workflow version, permissions, artifact
handoff and required-check names are verified in integration runs under
CLAUDE.md §8.12; branch protection keeps `strict=false`.

## D5-T0017: deployment boundary

`StrataLint topology` reads the workflow at the resolved remote default-branch
commit and checks the CI workflow and its current pull-request
contract. Its `STEADY-STATE-ACTIVE` result describes reachable topology; it does
not prove that a run executed that version or that branch protection is configured.
Deployment and protection state need their own observed evidence.

SL-022 evaluates raw changed paths before candidate-controlled inputs. Git rename and
copy records contribute both endpoints, so removing or moving a protected old path is
still a meta change. Engine, rules, emitters, CLI, tests, gate scripts, and workflows
retain their protected status. Declarative instances live outside
assemblies in their canonical TOML/Lean locations; shared program schema lives with its
smallest runtime owner. External review and branch protection remain human authorization;
neither candidate files nor a successful candidate test job can synthesize approval.

## FILEMAP custody boundary

`Meta/FILEMAP.toml` is the single manifest authority: `files` entries own path
membership, custody, admission plane, symlink declarations and optional
`digestion_source` eligibility. `evidence.artifact_kinds` owns format profiles,
selectors and coordinate scopes, including reserved formats. `Meta/domains.yaml`
remains the strict controlled domain vocabulary. Membership is followed by canonical
path/GID and domain validation; ambiguous or missing membership fails closed.

FILEMAP also declares each path's required resources and their explicit owners,
tools, cache layers and materials. These registrations govern planning without
discovering dependencies from code.

Engine owns the current-schema model, parser, canonical policy writer and generated
artifact identity inventory. FileMap, Scribe emitters and snapshot digests consume the
same path, producer and artifact-id contract; FILEMAP owns disposition and admission.
Scribe projects the validated model.

`make filemap-conform` builds and runs the FileMap executable with Configuration,
Engine and their necessary lower dependencies. The aggregate CLI consumes FileMap's
command implementation. `FILEMAP_SCOPE` and `FILEMAP_PRODUCER` select the scope and
committed write-set queries. Whole-tree checks read candidate actor sources, including
Scribe, without compiling or loading Scribe, QuestPDF, Jint or Acornima.
Current writes use schema 6 and a deterministic TOML encoding. Canonical snapshots use
schema 2 with `filemap_sha256`, binding the validated FILEMAP policy. Changed policy
bytes and structured Evidence are checked at the write boundary; unrelated deltas do
not replay historical byte canonicality. Narrow historical admission-plane and symlink
readers consume their own snapshot's metadata without imposing the current write
schema on a protected base. Projections retain their declared run-local residency.
