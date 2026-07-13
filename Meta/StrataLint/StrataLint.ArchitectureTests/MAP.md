# StrataLint.ArchitectureTests Map

## Buckets

- `Capabilities/`: unforgeable capability construction and its executable red fixture.
- `CanonicalSources/`: source-level checks that C# consumes canonical repository data instead of copying it.
- `Dependencies/`: compiled assembly dependency direction and whitelist fixtures.
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
- Public DSL/builders: rejects a literal default parameter value matching the `Gid`,
  `CaseId`, canonical anchor, or historical GICT/PZG anchor syntax on an effectively
  public member of an effectively public type named `*Dsl` or `*Builder`.

Each enabled family has a rejecting red fixture, a non-matching green fixture, and a
repository-wide zero-finding test.

### Open (not covered)

- Arbitrary semantic duplication, including split, encoded, concatenated,
  interpolated, or computed values.
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
- Other canonical families, including rule-catalog members, without a separately
  justified low-false-positive syntax criterion.
