# StrataLint trust topology

Production harness projects, scripts, manifests, and architecture material live under
`tools/`; all harness test and compile-fail projects live under `tools/tests/`.
`Meta/` is the data side of this boundary and contains no harness program directory.

`Meta/ci-units.json`, registered in FILEMAP, is the authority for CI selection,
required-check names, TOWER engineering members, and CI gate roots.
`ci_units.py` expands shared inputs, the unit workflow, explicitly registered
project includes and transitive references, and unit inputs into bash patterns.
Project exclusions do not narrow this selection; registered includes under a
`closure_excludes` prefix (Blueprint content, judged by `current`) stay out of
project closures unless a unit lists them in its inputs. The resolver requires the
run's `github.workflow_ref` and rejects a unit called from any workflow other than
the one registered for it. `ci-entry.sh` consumes the
resolved patterns through `CI_HIT_PATHS_FILE`; the entry verifies
the checked-out `GITHUB_SHA`, the complete event range and the pull-request merge
parents before deciding whether the unit is hit. A miss skips that unit and exits
successfully. Workflows run in parallel; steps within one workflow may be serial.
The entry removes remote state after the fixed candidate and any required base data
are available, and no workflow executes protected-base code.

`ci-unit.yml` supplies the common checkout, path hit, .NET and optional Lean cache
steps. Test units run the fixed registered-project make command; non-test units
supply their command in the caller workflow. Test projects, selftests,
compile-fail proofs, FILEMAP and current each have
their own workflow. `ci-current.yml` produces one Lean report and runs
`check-current`, Scribe, and (for pull requests) `check-delta` against the first
parent as data. `ci-filemap.yml` owns FILEMAP conformance. Every independent
workflow registers its required check in `Meta/ci-units.json`: reusable units
use `<id> / unit`, current uses `current`, and delta and publication-verify use
null. Non-null names are unique; `ci_units.py contexts` emits them in registration
order for ruleset configuration. Installed protection and actual execution remain
observations of the ruleset and real Actions runs.

TOWER engineering-ci declares only `members_from: ci-units`. Its members are the
ids whose check ends in ` / unit`; each must have the same job id and name in its
registered workflow. Every `ci-*.yml` except ci-unit.yml must be registered.
Report-ci and dev-baseline retain explicit members. Gate roots combine the
non-CI static roots in `Golden/gate-authority-roots.toml` with one
`<workflow filename>/<unit id>` root per non-null check, using its workflow as
the entrypoint. The combined roots are unique and sorted by UTF-8 root_id. C#
consumers fail closed on missing or malformed inventory fields; ci_units.py owns
complete registration validation.

Local validation uses the same independent commands: `make test` runs
`lean-report` and `check-current`, while `make gate BASE=<40-hex-commit-sha>` runs
those plus Scribe, FILEMAP and explicit-base `check-delta`. A project-specific
test is run with `make -C tools test TEST_PROJECT=...`; local success is early
feedback and does not replace remote required checks.

`StrataLint.TestEvidence` owns `list-test-owner-assemblies`, `verify-trx`, and
`compile-proof`. It references only Engine; its project closure contains neither
Scribe nor Scribe.Documents. `dotnet-test.sh` and the compile-proof make target
build and invoke this executable. CLI forwards the same commands through a project
reference. TRX validation requires successful executed tests, the selected owner
assemblies, and no infrastructure hang guard skips. The tool's owned tests also
compile into the existing CLI integration test project through an explicit source
link, so that CI unit executes both entrypoints' regression checks.

Report compatibility is the explicit `report_cache_release_semantic_version` in the registered
`lean-report-inputs.json`. Native Lake facets own report reuse and always require
the default Lean/audit targets and current inspector build. Lake traces and the explicit
cache release version decide reuse; validators check structure and artifact integrity
without comparing stored source digests with current repository bytes. Reused rows retain their actual producer
origins. Native report artifacts travel with `.lake/build` in the project snapshot;
there is no separate report cache or preparation shortcut. Remote seed compatibility
remains the resolved mathlib revision, with OS/architecture binary isolation.
`ci-current` builds the report once and transports it with the project build directory;
the split workflows consume their own unit results and do not select another report run.

No release command selects a CI run or report artifact. Truth-release bundles are
verified offline from their declared source and digest; eligibility and branch
protection remain separate observations. Workflow version, permissions, artifact
handoff and required-check names are verified in integration runs under
CLAUDE.md §8.12; branch protection keeps `strict=false`.

## D5-T0017: deployment boundary

`StrataLint topology` reads the workflow at the resolved remote default-branch
commit and checks the independent workflow family and current pull-request
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

Engine owns the pure current-schema model, parser and canonical policy writer. CLI
acquires bytes and joins the domain vocabulary; Scribe projects the validated model.
Current writes use schema 6 and a deterministic TOML encoding. Canonical snapshots use
schema 2 with `filemap_sha256`, binding the validated FILEMAP policy. Changed policy
bytes and structured Evidence are checked at the write boundary; unrelated deltas do
not replay historical byte canonicality. Narrow historical admission-plane and symlink
readers consume their own snapshot's metadata without imposing the current write
schema on a protected base. Projections retain their declared run-local residency.
