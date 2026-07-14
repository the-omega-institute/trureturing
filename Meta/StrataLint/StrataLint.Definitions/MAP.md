# StrataLint.Definitions Map

This assembly is the typed data layer. It depends only on the .NET platform plus the
pinned Tomlyn parser and owns the minimal schema needed to express its data without a
dependency cycle back through Scribe.

- `Catalog/`: canonical theory, specification, and external anchor definitions.
- `Values/`: the fourteen canonical value definitions and their computation descriptors.
- `Golden/`: closed mutation/diagnostic schema plus fail-closed canonical TOML
  loader/writer. Case data lives only in `Meta/StrataLint/Golden/cases`; execution
  lives in the CLI so tests, record mode, and Component C share one runner.
- `Schema/`: anchor and exact-rational construction types shared with Scribe.

Emitters, evaluators, kernels, rule execution, and test runners are program logic and do
not belong here. A separate `StrataLint.Schema` assembly is not justified this round:
the only shared schema pressure is small and already has a single downward owner here.

Scribe keeps a build-order-only project reference plus an assembly reference to this
output. Local data assembly membership therefore does not rewrite Scribe's NuGet package
lock, whose raw bytes are an attested input of the unchanged values projection.

When typed TOWER or BACKFILL definitions first exist, their canonical data belongs in
this assembly. No empty bucket is created before that pressure exists.
