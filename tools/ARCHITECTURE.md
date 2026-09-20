# StrataLint trust topology

Production harness projects, scripts, manifests, and architecture material live under
`tools/`; all harness test and compile-fail projects live under `tools/tests/`.
`Meta/` is the data side of this boundary and contains no harness program directory.

CI and preflight execute the candidate's programs. A PR uses the read-only
`pull_request` entry in `ci-pr.yml`; the first checkout uses the event's immutable
`github.sha` merge commit M. Before publishing a plan, `ci.py resolve` verifies
that checked-out HEAD equals `GITHUB_SHA`, has two parents, and has the triggering
PR head H as its second parent. It takes B from M's first parent. Every downstream
job checks out that same M; a later update to `refs/pull/N/merge` cannot select a
different candidate. Base commits supply data to the candidate judge, never code
that is restored, compiled, or executed.

The resolver publishes the complete plan and changed-path manifests together as
one Actions artifact. Job outputs carry only immutable candidate/base identities
and the artifact ID. Each consuming job downloads the files and validates their
complete scope and declared resource selection against the fixed candidate before
routing work. Missing, corrupt, or mismatched manifests fail even for no-resource
changes; path lists never travel through process arguments or environment values.

Push checks the final commit H. Its lightweight planner uses the push event's
complete before-to-after path range; initial pushes cover the registered current
tree. FILEMAP and explicit manifests select resources, build roots, tests, checks,
and cache layers. The semantic `current` checks have no baseline or changes input;
only PR `delta` checks compare B to M. Local PR preflight constructs an isolated
merge-tree candidate from a clean checkout and an explicit base SHA.

The common build stage restores locked packages, builds the selected candidate
projects, and seals their identity and outputs. Engineering accepts verified test
evidence and runs required selftests and negative compilations. Current enters the
incremental Lean/report producers when required, then checks Scribe, FILEMAP, and
current invariants. Delta consumes this round's validated common results and test
coverage. Reports, DLLs, TRX, and check materials are bound to the candidate and
production round before downstream use. Cache seeds are optional inputs to those
validators and producers; cache hits do not issue a passing verdict. PR runs do
not publish cache snapshots.

Report compatibility is the explicit `report_cache_release_semantic_version` in the registered
`lean-report-inputs.json`. Native Lake facets own report reuse and always require
the default Lean/audit targets and current inspector build. Lake traces and the explicit
cache release version decide reuse; validators check structure and artifact integrity
without comparing stored source digests with current repository bytes. Reused rows retain their actual producer
origins. Native report artifacts travel with `.lake/build` in the project snapshot;
there is no separate report cache or preparation shortcut. Remote seed compatibility
remains the resolved mathlib revision, with OS/architecture binary isolation.

PR required checks are `push / engineering`, `push / current`, and `delta`;
push required checks are `engineering` and `current`. The shared build job is a
prerequisite of its selected consumers. Truth release selects the two successful
push checks and report artifact for one explicit dev commit. Workflow version,
permissions, artifact handoff, and actual required-check names are verified in
integration runs under CLAUDE.md §8.12; branch protection keeps `strict=false`.

## D5-T0017: deployment boundary

`StrataLint topology` reads the workflow at the resolved remote default-branch
commit and checks its declared `pull_request` trigger and `delta` job. Its
`STEADY-STATE-ACTIVE` result describes reachable workflow topology; it does not
prove that a run executed that version or that branch protection is configured.
Deployment and protection state need their own observed evidence. The original
trusted-bootstrap boundary does not authorize executing a baseline judge or
bypassing the current integration and PR requirements.

SL-022 evaluates raw changed paths before candidate-controlled inputs. Git rename and
copy records contribute both endpoints, so removing or moving a protected old path is
still a meta change. Engine, rules, emitters, CLI, tests, gate scripts, and workflows
retain their protected status. Declarative instances live outside
assemblies in their canonical TOML/Lean locations; shared program schema lives with its
smallest runtime owner. External review and branch protection remain human authorization;
neither candidate files nor a successful candidate test job can synthesize approval.

## FILEMAP custody boundary

`Meta/FILEMAP.toml` owns repository file kind and producer/consumer/verifier relations.
It remains separate from `Meta/registry.yaml`: the registry has a strict semantic-coordinate
and artifact-kind schema, while FILEMAP has a strict file-custody schema. The architecture
suite joins them by requiring registry `root_files` to equal tracked root files, without
copying either schema into the other. The registry lists the FILEMAP authority and its
generated projection as governance documents. FILEMAP also declares each path's
required resources and their explicit owners, tools, cache layers, and materials;
these registrations govern planning without discovering dependencies from code.
