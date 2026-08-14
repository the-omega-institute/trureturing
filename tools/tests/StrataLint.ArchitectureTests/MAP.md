# StrataLint.ArchitectureTests Map

## Buckets

- `Capabilities/`: unforgeable capability construction and its executable red fixture.
- `CanonicalSources/`: source-level checks that C# consumes canonical repository data instead of copying it.
- `CanonicalSources/Golden/`: closed-stratum consistency policy, split locally when
  the parent bucket reached its file limit.
- `CanonicalSources/FileMap/`: FILEMAP closed-world coverage, producer/loader identity,
  data residence, class-directory purity, and dependency-direction fixtures.
- `CanonicalSources/RepositoryEnumeration/`: Git-index-backed tracked-file enumeration
  shared by canonical-source policies.
- `Capacity/`: repository capacity policy and its explicit exclusions.
- `Dependencies/`: compiled assembly dependency direction, retired-assembly absence,
  final source ownership, and whitelist fixtures.
- `Determinism/`: banned-API analyzer configuration and coverage.
- `PublicSurface/`: the exact exported Engine type allowlist.
- `RepositoryIo/`: production repository access and derived test-map policies.

The root contains only shared repository discovery, test metadata, and this map.

## Canonical-source boundary

### Covered

- Existing repository file paths: scans every `.cs` outside `.git`, `.lake`, `bin`,
  and `obj`; rejects a string literal containing at least two `/` characters when its
  value exactly equals an existing repository-relative file. A literal that directly
  initializes a `const string` is the machine-defined canonical-definition exemption;
  consumers must reference the constant.
- `Meta/domains.yaml`: rejects a C# dictionary indexer whose literal key is a
  registered domain and whose literal value is any `S0` through `S4` stratum code.
- Closed-stratum alphabet: a consistency anchor keeps `GoldenStratum`, Engine
  `Stratum`, and both closed `IsStratum` predicates equal to the explicit `S0`
  through `S4` five-member alphabet.
- FILEMAP: production `StrataLint filemap-conform` checks every tracked file against
  exactly one `Meta/FILEMAP.toml` pattern, aligns registry roots, joins generated
  inventory, resolves actors and data verifiers, enforces declared modes and directory
  kinds, closes run-local tracking and residence drift, and validates dependency and
  `.gitignore` policy. Architecture tests retain synthetic red/green fixtures for the
  production policy rather than scanning the repository.
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
- Theory isolation: scans all Lean files and every non-ingestion C# source; rejects
  internal theory paths and retired internal theory family tokens. The whitelist is
  limited to the atomizers, digestion status, ledger/schema validation, and their
  focused tests.
- External anchor reference: a `mathlib/module` anchor declared in a Lean header must
  be reachable through that file's repository import closure; an anchor shape the
  import graph cannot decide is rejected.
- Anchor definition names: every public typed anchor property is checked by reflection
  against a fixed scheme-specific transform. Literature uses a Pascal-cased bibkey;
  mathlib uses the Pascal-cased terminal qualified name followed by target kind.

Each syntax policy has a rejecting fixture, a non-matching green fixture, and a
repository-wide zero-finding test.

### Open (not covered)

- Backfill case/GID pair duplication: `BackfillInventoryLoader.RelativePath` still
  names the absent legacy `Meta/BACKFILL.yaml`; the current ledger is sharded under
  `Meta/Digestion/backfill/`, so the legacy exact-pair policy has no canonical object
  to compare against.
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
