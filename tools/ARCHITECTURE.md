# StrataLint trust topology

Production harness projects, scripts, manifests, and architecture material live under
`tools/`; all harness test and compile-fail projects live under `tools/tests/`.
`Meta/` is the data side of this boundary and contains no harness program directory.

The admission judge is selected before candidate policy, assemblies, or helpers are read.
The steady-state workflow is orchestrated by base-controlled `pull_request_target`, not
the candidate's workflow definition; candidate checkout credentials are not persisted.
The baseline is resolved from the checked object itself, never from the event payload:
both PR merge refs and `dev` push commits carry their protected base as the first parent,
so the baseline is `git -C candidate rev-parse HEAD^1` and the candidate is
`git -C candidate rev-parse HEAD`. Only `head` and `base` are admissible git references. A Lean-native predecessor job builds the candidate tree and
emits its source-bound canonical report. It uploads the report, SHA-256 sidecar, and
complete phase logs. The .NET admission job downloads and verifies that artifact, builds
the candidate judge with locked dependencies, and runs its DLL from the candidate repository
with `check --protected-base <dev-baseline-sha> --candidate-lean-report <file>`. The admission
job installs no Lean tooling and starts no Lean process. Candidate build, tests, and
selftest are engineering signals only and cannot issue admission.

## D5-T0017: one-time bootstrap

The first C# harness has no earlier C# judge, and a candidate-only
`pull_request_target` workflow cannot run before that workflow exists on the actual
default branch. Therefore the initial placement is not machine admission. It is a
one-time, human-authorized trusted bootstrap: an admin places the harness and this
workflow on `dev` without claiming predecessor harness verification. Any bootstrap push
run that selects the candidate is only a post-injection observation and says so in its
annotation and job summary.

`StrataLint topology` queries `origin HEAD`, reads the workflow from that exact remote
default-branch commit, and validates the `pull_request_target` trigger for that branch
plus the `baseline-admission` job. Until those are reachable on `dev`, it exits through
the human-gate path and reports
`BOOTSTRAP-NOT-ACTIVE:baseline gate 尚未注入 dev,当前非机器门控态,须人类可信注入(D5-T0017)`.
Only the reachable base workflow is reported as `STEADY-STATE-ACTIVE`.

After injection, the admin must configure `required_status_checks` for the baseline
admission job and set `enforce_admins=true`. Those hosting changes are caller-owned human
authorization under D5-T0017, not actions repository code can perform or verify by
itself. D5-T0017 remains open until the injection and settings are externally verified.
Afterward, the content-addressed dev-baseline harness adjudicates every later PR. If any
earlier dev commit contained the harness, a missing baseline harness is an infrastructure
failure and the trusted bootstrap path cannot recur.

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

Engine owns the pure current-schema model, parser and canonical policy writer. CLI
acquires bytes and joins the domain vocabulary; Scribe projects the validated model.
Current writes use schema 3 and a deterministic TOML encoding. Canonical snapshots use
schema 2 with `filemap_sha256`, binding the validated FILEMAP policy. Changed policy
bytes and structured Evidence are checked at the write boundary; unrelated deltas do
not replay historical byte canonicality. Narrow historical admission-plane and symlink
readers consume their own snapshot's metadata without imposing the current write
schema on a protected base. Projections retain their declared run-local residency.
