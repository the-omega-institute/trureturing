# Agent Context

Theory: D5 studies the golden integer/Zeckendorf coordinate system and its formal, narrative, and experimental consequences without promoting either open heart O-5/O-6. W1 uses Fibonacci weights `1,2,3,5,...`; W2 permits no adjacent occupied weights; W3 says the canonical W digits decode uniquely to the original natural number.

Map: `D5/` is the only M0 formal instance; `Blueprint/` and `Evidence/` mirror its addresses; `Chronicle/` is append-only; `Library/` ingests; `Papers/` emits; `Meta/` holds the harness; `agents/` holds charters. `Metallic/`, `Moduli/`, and non-D5 theory roots remain gated by D5-T0009. Controlled domains and strata live only in `Meta/domains.yaml`.

1. Route: write a flat manifest with exactly `theory`, `plane`, `domain`, `module`, `generality`, `selector`, `artifact`, and `tag`, then run `Meta/StrataLint route <manifest>`. GID grammar is `THEORY/[PLANE/]PATH[.selector][--tag]`; F omits `F`, E requires a selector plus artifact kind, and P uses `--frozen` for its frozen manifest.
2. Edit: create only the returned path and use its plane-specific `skeleton`. Only F receives the exact six-line Lean header. Machine fields are ASCII; modules/types are CamelCase; theorem names are snake_case; prose may be Unicode; never hand-write status. The sole normative specification is `docs/develop/spec/golden-ledger-repo-spec.md`.
3. Check: run `Meta/StrataLint check`, `Meta/StrataLint check --selftest`, and `lake build`. In a clean candidate checkout, pass the protected revision with `--protected-base <rev>`. Admission requires all commands to exit zero and the rule report to name every active or case-backed deferred rule.
