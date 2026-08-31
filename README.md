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

`worktree` fetches a remote base and creates the worktree with no `.lake` directory.
The canonical Lean wrapper materializes a private cache on demand, using an APFS
`clonefile(2)` donor copy on macOS when possible and `lake exe cache get` otherwise;
`make lean-cache-ensure` is an explicit, optional prewarm target. The cache is never
shared through a symlink, and worktree creation restores locked .NET dependencies
unless `--skip-restore` is explicit.

<!-- ci payload: top-level touch makes base_full_required=true so the #4393 integration base runs the real protected-base FULL path; deleted with the integration branch -->
