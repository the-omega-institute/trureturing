# Registration migration generator

The Lean readers load existing compiled inputs and parse each source file with
its own import environment. Source commands are neither elaborated nor
executed. The readers depend on Lean, Lake and the Reg interface package;
they do not import the judge implementation. Python consumes the resulting
UTF-8 byte spans and plans fixed Contract literals.

Build the readers and run the focused tests through the package doors:

```sh
make -C tools/reg-migration lean
make -C tools/reg-migration test
make -C tools/reg-migration test-parser
```

A capture manifest supplies `repo`, `files` (objects with repository-relative
`path` fields), `modules` (the corresponding module names) and
`syntax_snapshot` (the parser output filename). Optional `jobs` limits concurrent
parser children to 1–8 (default 4). Parse the files with isolated
per-file processes:

```sh
make -C tools/reg-migration parse MANIFEST=/path/to/manifest.json OUTPUT=/path/to/syntax.json
```

Read the compiled inputs with a separate native process:

```sh
make -C tools/reg-migration extract MANIFEST=/path/to/manifest.json OUTPUT=/path/to/inputs.json
```

Both executables load existing olean files; missing or stale inputs fail with a named diagnostic. The source hash in each
Lake trace and its recorded olean output are checked before a source binding
is exported. Registration and enrollment inputs also retain the source bytes
captured when the original commands compiled.

The planner requires the raw input and parser snapshots, not a judge report:

```sh
python3 tools/reg-migration/generate.py plan \
  --repo /path/to/repository --inputs /path/to/inputs.json \
  --syntax /path/to/syntax.json --mapping /path/to/root-kind-mapping.json \
  --output /path/to/dry-run
```

`--input-sha256` pins the raw snapshot. Math terms use original parser spans;
missing implicit terms require a closed, controlled Lean printer result with
full names and explicit universes. `controlled_printing` lists the fields that
use that fallback. Typed compiled Options preserve inherited and scoped
values; source option text is not an input to their encoding. Root occurrence
arrays retain their input order. SourceSelection uses its expanded compiled
metadata, including when the original selection was a reference.

Legacy, forward, witness, source, finite-source, occurrence and native
registrations share a renderer. Template enrollment, root literal and
reference entries, and seals use the same source/input bijection checks.
Catalog mapping authorizes root relocation and contributor ownership; mirror
registrations keep their original owners. Required Contract imports are
inserted while the surrounding mathematical context is retained.

`source_specializations` records edits to Lean AST identifier and universe
spans that attach the levels captured in the compiled input. The source
heads and other text remain intact; conflicting universe mappings fail.
Declaration binders reuse ambient source universes, and every emitted
declaration replays the complete original scoped prefix, including local
instances and options.

Stdout and the audit JSON include one `reconciliation` row for each compiled
registration, template, root and seal. Rows identify the owner and input
index, original command byte span, output path and declaration, and retained
identity. Root rows retain ordered occurrence identities and their original
and relocated registration owners. Equal theorem names remain separate
input rows. Failed plans publish no successful reconciliation rows.

Every input is reconciled before output. Unknown syntax, missing material,
source mismatch, duplicates, conflicting names and invalid owners return a
named failure with no target writes. `--apply` names an explicit target tree
and performs a complete preflight before atomic file replacement. Existing
identical output is not rewritten; a migrated tree produces zero edits.
Output is independent of input row order, current directory and host paths.
D5 is outside the write set. Full candidate checks and verdict comparison
remain separate consumers of the generated migration.
