# A5.6 — Reg package admission

This specification supplements A5.6 of `golden-ledger-repo-spec.md` for the independent declaration package.

`Reg/lakefile.toml` and `Reg/lake-manifest.json` are program artifacts on the judge admission plane. The empty `Reg` library is lawful; it requires no dummy module. Its library has `srcDir = ".."`, roots `["Reg"]`, and globs `["Reg.+"]`. Outputs use `../.lake/build/reg`, and dependencies share `../.lake/packages` with the repository root.

Before cache ensure or writer admission, and in current-tree structural configuration validation (SL-015), the harness reads both manifests as data. The multiset of git tuples `(name, url, rev, inputRev, subDir, configFile, manifestFile)` must equal the root manifest, and every Reg git package is inherited. Reg has exactly three non-inherited path entries: `trureturing` at `..` with `lakefile.toml`, `leanInspectorInterface` at `../tools/lean-inspector-interface` with `lakefile.toml`, and `leanInspector` at `../tools/lean-inspector` with `lakefile.lean`; each uses `lake-manifest.json`. `packagesDir` is exactly `../.lake/packages`. A lakefile without its manifest, malformed input, or any disagreement fails closed before Lake may materialize shared dependencies.

The only declaration source families are `Reg/D5/**/*.lean`, `Reg/Support/**/*.lean`, and `Reg/Catalogs/**/*.lean`. These are content-plane executable declaration data with supporting kernel proofs, verified by `lean-build` and `lean-inspector`. The suffix after `Reg/` for a D5 mirror must satisfy the existing D5 formal path grammar and controlled stratum/domain relation. Support and catalog paths consist of CamelCase module segments. Package configs and the three source families have disjoint FILEMAP entries.

A Reg source is a report member, with module name obtained by removing `.lean` and replacing `/` with `.`. Report membership does not confer mathematical identity: Reg is not a stratum or a GID theory. Reg sources carry no Scribe, GID, canonical Lean header, mathematical deposit, or computational utility (SL-031) duties. They are excluded from D5 theorem candidates and mathematical truth projections. Their supporting proofs remain subject to kernel, sorry and axiom checks; a mirrored frontier path grants no exception.

The report selection includes optional `Reg/**/*.lean` and requires the two package configuration files once introduced. With no Reg modules, raw report content is unchanged. This admission does not change report version, reuse, or per-module traces.

Build/report entry points, report-facet repository-root derivation, and anchoring the judge's source reads independently of its working directory are subsequent integration work. Until those are implemented, root builds/reports stay at the root, and the only permitted Reg workspace build probe is `lake build --no-build @trureturing @leanInspectorInterface Reg`.
