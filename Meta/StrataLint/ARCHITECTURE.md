# StrataLint trust topology

The admission judge is selected before candidate policy, assemblies, or helpers are read.
The steady-state workflow is orchestrated by base-controlled `pull_request_target`, not
the candidate's workflow definition; candidate checkout credentials are not persisted.
For pull requests targeting `dev`, the baseline is the exact
`github.event.pull_request.base.sha`; for pushes to `dev`, it is the exact
`github.event.before` SHA (or the candidate parent when the first branch-creation event
has an all-zero `before`). A Lean-native predecessor job uses the base producer to build
both trees and emit source-bound canonical reports. It uploads the reports, SHA-256
sidecars, and complete phase logs. The .NET admission job downloads and verifies those
artifacts, builds the content-addressed baseline judge with locked dependencies, and runs
its DLL from the candidate repository with `check --protected-base <dev-baseline-sha>`
plus `--candidate-lean-report <file>` and `--baseline-lean-report <file>`. The admission
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
retain their protected status. The retired `StrataLint.Definitions/` prefix remains a
recorded bootstrap exception because the v1 predecessor codec validates candidate
SL-022 diagnostics with the predecessor predicate; the architecture suite separately
forbids that directory and assembly from returning. Declarative instances live outside
assemblies in their canonical TOML/Lean locations; shared program schema lives with its
smallest runtime owner. External review and branch protection remain human authorization;
neither candidate files nor a successful candidate test job can synthesize approval.

## FILEMAP custody boundary

`Meta/FILEMAP.toml` owns repository file kind and producer/consumer/verifier relations.
It remains separate from `Meta/registry.yaml`: the registry has a strict semantic-coordinate
and artifact-kind schema, while FILEMAP has a strict file-custody schema. The architecture
suite joins them by requiring registry `root_files` to equal tracked root files, without
copying either schema into the other.

`Meta/StrataLint/` is normatively a program-only protected surface. The open
`RESIDENCE-EPOCH` records five current `kind=data` files under
`Meta/StrataLint/Golden/`; their two FILEMAP entries carry
`residence_violation=true`, and the architecture suite freezes the exact expanded file
set so an unmarked or additional violation fails. Blueprint Scribe sources and the
Golden residence remain under the predecessor SL-022 protection contract in this epoch.
Moving cases, values, and C0/frozen material to top-level `Golden/` is deferred until an
sshx-reviewed verifier mechanism can approve protection-surface contraction.
