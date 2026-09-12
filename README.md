[![Explore & Contribute](https://img.shields.io/badge/Explore_%26_Contribute-0d1117?style=flat-square&logo=data%3Aimage%2Fsvg%2Bxml%3Bbase64%2CPHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAxMDAgMTAwIj48ZyBmaWxsPSJub25lIiBzdHJva2U9IiM0ZmQxYTEiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCI%2BPHBhdGggZD0iTTcxIDcxQTMwIDMwIDAgMSAwIDI5IDcxIiBzdHJva2Utd2lkdGg9IjExIi8%2BPHBhdGggZD0iTTcxIDcxIDYxIDU5IDUwIDcxIDM5IDU5IDI5IDcxIiBzdHJva2Utd2lkdGg9IjEwIi8%2BPHBhdGggZD0iTTQ2IDQ0SDU0IiBzdHJva2Utd2lkdGg9IjQiLz48L2c%2BPGcgZmlsbD0iIzRmZDFhMSI%2BPHJlY3QgeD0iMzAiIHk9IjM4IiB3aWR0aD0iMTciIGhlaWdodD0iMTIiIHJ4PSI0Ii8%2BPHJlY3QgeD0iNTMiIHk9IjM4IiB3aWR0aD0iMTciIGhlaWdodD0iMTIiIHJ4PSI0Ii8%2BPC9nPjwvc3ZnPg%3D%3D)](https://bot.chrono-ai.fun/api/v1/triggers/public/pub_d77caf24c76f4ce188e569a83c71b8a1/open/plc_0571014f545848dbb8ed00c49a532fac)

trureturing — the last line of the ledger is always the first line of the next round.

The `Blueprint/` Markdown content of this repository is published as a browsable, searchable
mdBook site at **<https://the-omega-institute.github.io/trureturing-mdbook/>**. That site is a
derived projection, rebuilt daily from this repository by
[the-omega-institute/trureturing-mdbook](https://github.com/the-omega-institute/trureturing-mdbook);
it is not a source of truth and holds no authority over anything here.

GitHub required-check configuration is a human gate and has not been verified by this repository.

Developer commands have one top-level entry point:

```text
make help
```

Harness programs live under `tools/`, harness tests under `tools/tests/`, and
canonical helper scripts under `tools/scripts/`. `Meta/` contains only FILEMAP,
registry/domain data, and the digestion ledger. The Makefile contains routing only.

StrataLint commands:

```text
tools/lean-inspector/inspect.sh --repository ROOT --output REPORT
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- check [--protected-base REV] --candidate-lean-report FILE
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- coverage [--json]
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- route MANIFEST|-
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- selftest
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- topology
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- worktree --branch NAME --path DIR [--base REV] [--skip-restore]
```

Lean inspection and .NET admission are separate programs. The inspector runs in
the pinned Lean environment and emits source-bound canonical JSON plus a SHA-256
sidecar; `check` consumes the candidate report without invoking Lean. Baseline and fork-point
state remain Git object snapshots used by repository rules.

`worktree` fetches a remote base and creates a worktree without `.lake`.
`make lean-cache-ensure` materializes private dependency sources. `make lean` and
`make lean-report` use native Lake artifact reads and restore ordinary `.lake/build`
outputs. Missing artifacts rebuild locally. Mathlib downloads live in each tree's
`.lake/mathlib-cache`; CI's GitHub release cache remains a separate private fallback.
Worktree creation restores locked .NET dependencies unless `--skip-restore` is explicit.

Only `make warm-donor` in the physical, clean main `dev` checkout publishes the local
shared store. It holds an exclusive warmer lock and the main `.lake` lock across
pull, ensure, build and publication. Locks live in canonical Git metadata, independent
of temporary-directory settings. Native Lake staging preserves older input
mappings; a bulk clone/copy detaches artifacts from mutable build outputs before
publication. Complete artifacts precede atomic per-file mapping replacement, so
readers remain usable during warming and failed publication preserves prior reads.

The shared store is `<git-common-dir>/stratalint-lake/lean-<version>/<os>-<arch>`.
Lake owns all content hashes; commits and manifest metadata do not partition it.
Normal commands, including main-checkout builds, clear inherited writer and cache
path overrides. On macOS, sandbox-exec denies writes to the canonical shared
subtree for the command and its descendants, forcing hardlink restores to copy.
If a package explicitly enables cache writes, a
Lake build rejected for writing the shared store retries once with a private artifact
cache; shared write denial remains in force.
Shared mode and warming currently require macOS with sandbox-exec. Other platforms
use private caches when no shared store exists and explicitly reject shared mode.
Existing private build outputs remain usable; donor cloning and reverse publication
are removed. `.lake` and its build/package/cache directories must not be symlinks.
