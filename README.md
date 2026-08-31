trureturing — the last line of the ledger is always the first line of the next round.

# trureturing

trureturing formalizes the golden integer/Zeckendorf coordinate system in Lean: Fibonacci
weights `1,2,3,5,...`, no adjacent occupied weights, and canonical digits that decode uniquely
to the original natural number. Accepted modules are appended to a frozen ledger; for each one
the harness derives a Merkle address from its module path, its statement, and the addresses of
its prerequisites, so changing an ancestor readdresses every descendant. The ledger carries a
frozen formalization of the [Three-Gap theorem](D5/S1/Phase/ThreeGap/Main.lean). At the
[frontier](D5/X_Frontier/Hearts.lean), `o5_independence` stops at a literal proof-body `sorry`,
while Weil positivity (classically equivalent to the Riemann Hypothesis) is named only as a
`Prop`, with no proof asserted.

## Frozen addresses

```text
[A] addr(A) = H("frozen-node-v2", module_path(A), statement_id(A), [])
                         |
                         v
[B] addr(B) = H("frozen-node-v2", module_path(B), statement_id(B), [addr(A)])
                         |
                         v
[C] addr(C) = H("frozen-node-v2", module_path(C), statement_id(C), [addr(A), addr(B)])
```

Each address is derived from the canonical JSON of these fields; it is not stored in the
ledger. A change to `addr(A)` changes the prerequisite material hashed for `B` and `C`.

## The frontier

[Hearts.lean](D5/X_Frontier/Hearts.lean) gives O-5 and O-6 distinct starting points for
further proof. O-5 is the theorem `o5_independence`; its body is the literal `sorry`, the
only proof-body `sorry` under `D5/`. O-6 is the definition
`o6WeilPositivityStatement : Prop`; it names Weil positivity as a proposition. It asserts
no theorem or axiom. The other two lexical `sorry` hits are comments in
[Foundations.lean](D5/S1/Phase/ThreeGap/Foundations.lean) and
[Main.lean](D5/S1/Phase/ThreeGap/Main.lean).

## The ledger

Measured on 2026-08-31 at commit `d343b970ac7450641e3697fb310e99e397083eab`:

| Object | Reading |
| --- | --- |
| Accepted history | 2,788 events; all `Freeze`; all `schema_version: 5` |
| Named theorem exhibit | [`ThreeGap/Main.lean`](D5/S1/Phase/ThreeGap/Main.lean) has an accepted `Freeze` event carrying `three_gap_card_le_three` and `three_gap_lengths_eq` |
| Coordinate route | 10 accepted `Freeze` events name module paths containing `ThreeGap` or `Zeckendorf` |

These readings reproduce from a checkout of the stamped commit.

## Build and verify

`make help` is the single command entrance and prints the current target vocabulary.
The content layer pins Lean `v4.31.0` and mathlib `inputRev v4.31.0`.
Three machine checks judge admission: `engineering`, `lean-inspect`, and `admission`;
enforcement on every GitHub merge is unverified.

## Read and navigate

Machine ownership is declared in [`Meta/FILEMAP.toml`](Meta/FILEMAP.toml); this list only
routes readers to what they will find.

- [`CLAUDE.md`](CLAUDE.md) contains the repository constitution in Chinese.
- [`agents/CONTEXT.md`](agents/CONTEXT.md) contains the compact repository map and workflow.
- [`docs/develop/spec/golden-ledger-repo-spec.md`](docs/develop/spec/golden-ledger-repo-spec.md) contains the repository specification.
- [`D5/`](D5/) contains the Lean formalization.
- [`Blueprint/`](Blueprint/) contains hand-written `Blueprint/**/*.scribe.cs` data; only
  `Blueprint/**/*.md` is emitted by `ScribeEmitter`. The
  [mdBook](https://the-omega-institute.github.io/trureturing-mdbook/) is externally built over
  those emitted files. Hosted freshness is unverified.
- [`docs/develop/theory/`](docs/develop/theory/) contains reference inputs.
- [`Problems/`](Problems/) contains open problems posted for outside attack.
