# StrataLint.ArchitectureTests Map

## Buckets

- `Capabilities/`: unforgeable capability construction and its executable red fixture.
- `CanonicalSources/`: source-level checks that C# consumes canonical repository data instead of copying it.
- `Dependencies/`: compiled assembly dependency direction and whitelist fixtures.
- `Namespaces/`: source path to namespace policy, including Blueprint linked-source conventions.
- `PublicSurface/`: the exact exported Engine type allowlist.

The root contains only shared repository discovery, test metadata, and this map.

## Canonical-source boundary

The current machine criterion loads `Meta/BACKFILL.yaml` through
`BackfillInventoryLoader`, scans repository C# outside `.git`, `.lake`, `bin`, and
`obj`, and rejects any exact canonical `case_id <-> gid` pair encoded in a C#
dictionary indexer (scalar, collection-expression, or array RHS) or two-element tuple
literal. This covers the ticket-map shape that previously existed in `RuleFixture`;
the red and green fixtures pin both detection and non-detection of unrelated
diagnostic literals.

This is intentionally not a proof against arbitrary semantic duplication. Equivalent
data split across files, encoded or computed literals, and the canonical domain,
registry, and rule-catalog families remain open for later, separately testable checks.
