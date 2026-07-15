# StrataLint.ArchitectureTests Map

## Buckets

- `Capabilities/`: unforgeable capability construction and its executable red fixture.
- `CanonicalSources/`: source-level checks that C# consumes canonical repository data instead of copying it.
- `CanonicalSources/Golden/`: golden TOML storage and closed-stratum consistency
  policies, split locally when the parent bucket reached its file limit.
- `CanonicalSources/FileMap/`: FILEMAP closed-world coverage, producer/loader identity,
  data residence, class-directory purity, and dependency-direction fixtures.
- `Dependencies/`: compiled assembly dependency direction, retired-assembly absence,
  final source ownership, and whitelist fixtures.
- `Namespaces/`: source path to namespace policy, including Blueprint linked-source conventions.
- `PublicSurface/`: the exact exported Engine type allowlist.

The root contains only shared repository discovery, test metadata, and this map.

## Canonical-source boundary

### Covered

- `Meta/BACKFILL.yaml`: rejects an exact canonical `case_id <-> gid` pair in a C#
  dictionary indexer (scalar, collection-expression, or array RHS) or two-element
  tuple literal.
- Existing repository file paths: scans every `.cs` outside `.git`, `.lake`, `bin`,
  and `obj`; rejects a string literal containing at least two `/` characters when its
  value exactly equals an existing repository-relative file. A literal that directly
  initializes a `const string` is the machine-defined canonical-definition exemption;
  consumers must reference the constant.
- `Meta/domains.yaml`: rejects a C# dictionary indexer whose literal key is a
  registered domain and whose literal value is any `S0` through `S4` stratum code.
- Golden corpus storage: rejects literal-name golden case construction in tracked C#;
  the only case authority is strict canonical TOML under
  `Meta/StrataLint/Golden/cases`. A separate consistency anchor keeps
  `GoldenStratum`, Engine `Stratum`, and both closed `IsStratum` predicates equal to
  the explicit `S0` through `S4` five-member alphabet.
- FILEMAP: every tracked or unignored file matches exactly one `Meta/FILEMAP.toml`
  pattern; registry root membership is equal to tracked root files; generated artifacts
  match the canonical producer inventory and `emit-check`; every data verifier resolves
  to an existing program file; generated and Golden class directories remain pure.
  The `RESIDENCE-EPOCH` sentinel expands marked FILEMAP entries and requires the current
  five protected-surface data paths to equal the frozen known-violation inventory.
- Dependency direction: machine-readable data is rejected when its decoded text names a
  concrete generated path, and a simple single-module Lean import is rejected when it
  resolves to a generated `.lean` file.
- Public DSL/builders: rejects a literal default parameter value matching the `Gid`,
  `CaseId`, or canonical external anchor on an effectively public member of an
  effectively public type named `*Dsl` or `*Builder`.
- Central package versions: rejects any tracked C# string literal exactly equal to a
  version owned by `Directory.Packages.props`.
- .NET SDK workflow pin: parsed `actions/setup-dotnet@*` steps must use
  `global-json-file` and may not copy a `dotnet-version` value.
- Theory isolation: scans all Lean files, every non-ingestion C# source, and the
  generated anchor catalog; rejects internal theory paths, retired internal theory
  family tokens, and retired catalog schemes. The whitelist is limited to the
  atomizers, digestion status, ledger/schema validation, and their focused tests.
- External anchor catalog: Scribe definitions and the generated catalog contain only
  literature bibkeys and mathlib modules or declarations, and the catalog definitions
  must exactly equal the external manifest.
- Anchor definition names: every public typed anchor property is checked by reflection
  against a fixed scheme-specific transform. Literature uses a Pascal-cased bibkey;
  mathlib uses the Pascal-cased terminal qualified name followed by target kind.
- ComponentC C0 ceremony: TOWER controller/corpus/gate Git blob OIDs and the inaugural
  certificate SHA-256 must match the canonical worktree bytes and the certificate's
  Git preimage; loader/schema C# and TOML corpus sets are recursively discovered from
  their owning directories so additions cannot escape the root.

Each syntax policy has a rejecting fixture, a non-matching green fixture, and a
repository-wide zero-finding test. C0 ceremony uses live repository-bound address
tripwires plus synthetic source-discovery fixtures; it does not currently have an
isolated byte-mismatch fixture.

### Open (not covered)

- Arbitrary semantic duplication, including split, encoded, concatenated,
  interpolated, or computed values.
- Split/interpolated/computed copies of central package or SDK versions.
- Whether an exempt `const string` is globally unique or semantically the best
  canonical owner; the rule proves only a single machine-visible definition point per
  consumption chain.
- Domain mappings expressed as tuples, `Add` calls, nested objects, or other shapes
  than a dictionary indexer.
- `Meta/registry.yaml` member duplication. Its list members are also legitimate test
  inputs and diagnostics, and no low-false-positive C# syntax shape currently
  distinguishes those uses from a copied registry.
- DSL/builder defaults supplied through constant references or other non-literal
  expressions, non-public APIs, or public APIs on types not named `*Dsl`/`*Builder`.
- External-catalog provenance claims beyond canonical syntax and byte-stable catalog
  membership.
- Encoded, concatenated, interpolated, or computed generated-path references, structured
  references outside TOML/YAML/JSON/Scribe inputs, and Lean import syntax beyond the
  single-module form checked by FILEMAP.
