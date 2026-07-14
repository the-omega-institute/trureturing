# Golden TOML Corpus Design

## Decision

The 110 StrataLint golden cases move from four `GoldenCorpus.Cases*.cs` files to
four behavior-domain TOML files under `Meta/StrataLint/Golden/cases/`. TOML is the
only authority for case names, baseline mutations, current mutations, expected
diagnostics, and changed paths. C# retains only the closed schema, loader,
canonical writer, fixture executor, and commands.

The final stratum ruling remains intact: `GoldenStratum` is a closed enum with
`S0` through `S4`. The loader parses TOML stratum strings against that enum with
case-sensitive `Enum.TryParse`; it does not add a YAML registry or runtime-derived
alphabet. One architecture test anchors the golden enum, the Engine enum, and
both existing `IsStratum` predicates to the same explicit five-member set.

## Data Shape

The four files are grouped as follows:

- `structure-and-identities.toml`: repository shape, imports, mirrors, headers,
  task identity, and address grammar.
- `digestion-and-anchors.toml`: BACKFILL, query anchors, and ledger entry cases.
- `structured-ledger.toml`: structured JSON/YAML canonicalization and anomaly
  accounting cases.
- `protected-semantics.toml`: values attestation, axiom closure, protected paths,
  and bootstrap cases.

Each file starts with the required ontology comment followed by a byte contract
comment. Canonical bytes are strict UTF-8 without BOM, LF-only, and exactly one
terminal LF. Cases preserve their source order. Case keys are emitted in the
order `name`, `changes`, `baseline_mutations`, `mutations`,
`expected_diagnostics`; mutation and diagnostic inline-table keys follow their
schema order. Strings use one canonical TOML basic-string escape form.

Every case declares all five case keys, including empty arrays. Mutation `op`
values are a closed one-to-one mapping of the current typed union:
`write`, `write_parts`, `lean`, `delete`, `append_lines`, `add_domain`,
`add_task`, `populate_directory`, `empty_mirror_waiver`, `evidence_mirror`,
`replace_backfill`, `replace_first_backfill_disposition`, and
`mutate_backfill_anchor`. The early `append_lines` declaration remains an
operation with `path`, integer `count`, and `line`; it is not expanded into
generated content.

## Loader And Writer

`TomlGoldenLoader` lives in Definitions and uses Tomlyn 2.10.1. It reads sorted
`*.toml` files and fails closed on invalid UTF-8, BOM, CR, missing terminal LF,
TOML diagnostics, unknown or missing keys, wrong scalar/container types,
out-of-range rule/count values, unknown operation names, operation-specific
extra or missing parameters, invalid generality, invalid stratum, empty names,
and duplicate case names across files. It then canonical-writes the parsed model
and requires byte equality with the input.

`TomlGoldenWriter` owns the byte convention and rewrites complete source files.
It is used both to generate the migration and by record mode. The writer does not
infer expectations or execute the Engine.

## Execution And Recording

One production-side golden fixture executor in the CLI assembly owns base fixture
construction, mutation application, synthetic Lean reports, and Engine context
construction. `GoldenCorpusMaterializer`, golden check tests, and the recorder
all call this executor, removing the current duplicate mutation switches in the
materializer and test fixture.

Normal check loads TOML, runs every mutation sequence through the current Engine,
and compares sorted rendered diagnostics with the stored snapshot. A mismatch is
a test failure. `StrataLint golden-record`, exposed only through
`make record-golden`, runs the same 110 cases and canonical-rewrites only their
`expected_diagnostics`. It does not commit, stage, or admit anything. CI continues
to call check paths only and never calls record, so recording remains visible as
a normal git diff requiring Component C and PR review.

## Architecture And Trust

Architecture tests replace the obsolete “canonical C# case data belongs in
Definitions” rows with a narrow policy that rejects golden case declarations in
tracked C# and verifies the canonical TOML directory. It includes a synthetic red
fixture and a green schema/executor counterfixture. The new hard-code family and
its authority are recorded in `HARDCODE-LEDGER.md`.

Component C corpus discovery includes the Definitions golden schema/loader/writer
and every canonical TOML case file. Materialization always calls the loader on
the supplied baseline root, so candidate data cannot replace the base-owned
corpus. After an implementation preimage commit, the conservative gate emits a
fresh 110-case `CORPUS_CONSERVATIVE` certificate; `TOWER.yaml` records the new
source blob OIDs, certificate digest, preimage commit, and preimage tree.

## Verification

Before migration, a scratch artifact records every typed case's expected
diagnostics and materialized case root. After migration, the same projection is
produced from TOML and compared by case name. Completion requires 110 names,
110 identical diagnostic snapshots, 110 identical materialized case roots, and
the same whole-corpus root. Loader tests cover one canonical green fixture plus
unknown-key, unknown-op, and wrong-type red fixtures. Final evidence also includes
`make dotnet`, `make test`, `make gate BASE=origin/dev` with
`CORPUS_CONSERVATIVE`, and `make emit-check`.
