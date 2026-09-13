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

Run the shared checks through Make:

```text
make preflight MODE=push
make preflight MODE=pr BASE=<40-hex-commit-sha>
```

Push preflight checks the current working tree. PR preflight requires a clean
working tree and an explicit base commit, constructs the candidate merge tree,
and checks it with the candidate's own programs. Merge conflicts fail immediately.
Without an explicit complete range, local push preflight selects all current
registered inputs; it does not infer a previous commit.
The three stage entries are `make -C tools engineering`, `make current`, and
`make delta BASE=<40-hex-commit-sha>`; delta consumes the current round's build,
test and report evidence. Only PR mode runs delta, and base revisions supply data.

FILEMAP registers which resources each path needs. A validated complete change
plan containing only paths with `require = []` produces a successful
`not-required` result without setting
up unnecessary SDKs or caches. Missing registration or incomplete change inputs
fail explicitly. A cache hit supplies reusable work; it does not establish that
a check passed.

Other StrataLint commands:

```text
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- coverage [--json]
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- route MANIFEST|-
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- selftest
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- topology
dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- worktree --kind KIND --name NAME --path DIR [--base REV] [--skip-restore]
```

Lean inspection and .NET admission are separate programs. The inspector runs in
the pinned Lean environment and emits source-bound canonical JSON plus a SHA-256
sidecar; the .NET `check-current` and `check-delta` commands consume the candidate
report without invoking Lean. `make lean-report` always enters incremental production and validates the
selected seed, module sources, dependencies and statement materials. Report
compatibility uses `compatibility_version` in `Meta/lean-report.toml`; increment
it when producer changes require old reports to be rejected. Producer source
bytes do not automatically change this version. The separate
`Meta/ReportProducers/lean-report.json` registers engineering and evidence inputs.
Neither identity changes the remote mathlib cache partition.

`worktree` fetches a remote base and creates the worktree with no `.lake` directory.
The canonical Lean wrapper materializes a private cache on demand, using an APFS
`clonefile(2)` donor copy on macOS when possible and `lake exe cache get` otherwise;
`make lean-cache-ensure` is an explicit, optional prewarm target. The cache is never
shared through a symlink, and worktree creation restores locked .NET dependencies
unless `--skip-restore` is explicit.

The dependency, project and report caches are partitioned by mathlib's resolved
revision in `lake-manifest.json` and binary platform; elan separately caches
toolchain installation. Lake owns the build hashes and input mappings. Commits,
project sources and complete manifest bytes do not partition these caches.
