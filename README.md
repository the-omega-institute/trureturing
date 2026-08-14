trureturing — the last line of the ledger is always the first line of the next round.

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

`worktree` fetches a remote base, compares the exact `lean-toolchain` and
`lake-manifest.json` bytes, and only then copies `.lake` from a matching worktree.
On macOS it first uses APFS clonefile (`cp -c -R`), reports and falls back when
clonefile is unavailable, and uses `lake exe cache get` when no pinned donor
matches. It never shares `.lake` through a symlink and restores locked .NET
dependencies unless `--skip-restore` is explicit.
