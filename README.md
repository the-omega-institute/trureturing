trureturing — the last line of the ledger is always the first line of the next round.

# trureturing

This repository is a formal-mathematics repository built as an irreversible truth DAG:
Lean carries its statements and proofs, a C# harness judges admission, and each accepted node
is frozen into an append-only ledger instead of being rewritten.

## Truth flow

```text
docs/develop/theory/ (reference input only) --ingest--> D5/
                                                     (Lean; sole mathematical source of truth)
tools/ (C# judge; no mathematical content) --judges--> D5/
tools/ --freezes accepted D5 nodes--> Golden/Frozen/accepted/ (frozen ledger)

Blueprint/**/*.scribe.cs (source; mirrors D5 addresses) --> ScribeEmitter
Library/*/*.md (source) ---------------------------------> ScribeEmitter
ScribeEmitter -------------------------------------------> Blueprint/**/*.md (generated)
```

## The ledger, measured

All readings in this file were measured on 2026-08-31 at commit `d343b970ac7450641e3697fb310e99e397083eab` and reproduce from a checkout of that commit.

| Reading | Value |
| --- | --- |
| Ledger file, event, and distinct-node counts | 2,788 JSON files; 2,788 events: 2,788 `Freeze`, 0 `Revoke`, 0 `Reattest`, all schema 5; 2,788 distinct `payload.statement_id` values |
| Content-addressed prerequisite edges | 2,737 edges; 855 roots; maximum 48 prerequisites on one node |
| Declarations carried by frozen nodes | 26,824 declaration records spanning 26,801 distinct names; by record kind: 14,461 `theorem`, 11,238 `def`, 490 `constructor`, 317 `inductive`, 317 `recursor`, 1 `opaque` |
| Lexical `sorry` hits in `D5/**/*.lean` | 3 hits: 1 proof body and 2 prose hits inside comments |
| Named frontier declarations in `Hearts.lean` | 2: `o5_independence` and `o6WeilPositivityStatement` |
| Pinned environment | Lean `v4.31.0`; mathlib `inputRev v4.31.0` |

The declaration figures count ledger declaration records; they make no claim of independence, importance, or novelty. The broad search reports 3 lexical hits: 1 proof body at
`D5/X_Frontier/Hearts.lean:76`, and 2 prose hits inside comments at `D5/S1/Phase/ThreeGap/Foundations.lean:48` and `D5/S1/Phase/ThreeGap/Main.lean:66`.

From the stamped checkout, one paste reproduces the table in order:

```bash
files=(Golden/Frozen/accepted/*.json)
python3 - "${files[@]}" <<'PY'
import collections, json, sys
events = [json.load(open(path)) for path in sys.argv[1:]]
prereqs = [event["payload"]["prerequisite_frozen_node_ids"] for event in events]; decls = [decl for event in events for decl in event["payload"]["declaration_statement_ids"]]
event_types = collections.Counter(event["event_type"] for event in events); kinds = collections.Counter(decl["kind"] for decl in decls)
print("ledger", f"files={len(sys.argv) - 1}", f"events={len(events)}", *(f"{kind}={event_types[kind]}" for kind in ("Freeze", "Revoke", "Reattest")), "schema=" + ",".join(map(str, sorted({event["schema_version"] for event in events}))), f"nodes={len({event['payload']['statement_id'] for event in events})}")
print("edges", sum(map(len, prereqs)), f"roots={sum(not ids for ids in prereqs)}", f"max={max(map(len, prereqs))}")
print("declarations", f"records={len(decls)}", f"names={len({decl['declaration_name_key'] for decl in decls})}", *(f"{kind}={kinds[kind]}" for kind in ("theorem", "def", "constructor", "inductive", "recursor", "opaque")))
PY
sorry_hits=$(grep -rn '\bsorry\b' D5 --include='*.lean')
sorry_total=$(printf '%s\n' "$sorry_hits" | wc -l | tr -d ' ')
sorry_proof=$(printf '%s\n' "$sorry_hits" | grep -cE ':[[:space:]]*sorry[[:space:]]*$')
printf 'sorry hits=%s proof=%s prose=%s %s\n' "$sorry_total" "$sorry_proof" "$((sorry_total - sorry_proof))" "$(printf '%s\n' "$sorry_hits" | paste -sd '|' -)"
printf 'hearts '; grep -Ec '^(theorem o5_independence|def o6WeilPositivityStatement) ' D5/X_Frontier/Hearts.lean
printf 'environment lean=%s mathlib=%s\n' "$(sed 's/.*://' lean-toolchain)" "$(jq -r '.packages[] | select(.name == "mathlib") | .inputRev' lake-manifest.json)"
```

## The open frontier

At the stamped revision, [D5/X_Frontier/Hearts.lean](D5/X_Frontier/Hearts.lean) contains the two frontier declarations printed here:

```lean
theorem o5_independence :
    ∃ Zqc : ℂ → ℂ,
      MeromorphicOn Zqc {s | 0 < s.re} ∧
      (∀ s : ℂ, 1 / phi ^ 2 < s.re → Zqc s = eulerGerm s) ∧
      ∀ s : ℂ,
        1 / (2 * phi ^ 3) < s.re →
        s.re < 1 / phi ^ 2 →
        AnalyticAt ℂ Zqc s →
        Zqc s = 0 →
        s.re = structuralZero := by
  sorry

def o6WeilPositivityStatement : Prop :=
```

The first is a theorem with the single proof-body `sorry`; the second defines a `Prop` and
supplies no proof. The module's docstring owns the remaining context.

## Build and verify

`make help` is the single live command entrance and owns the command vocabulary.

This repository defines its own admission checks and runs them in CI. It does not verify GitHub's required-check or branch-protection configuration, so it makes no claim that those checks are enforced on every merge.

## Read and navigate

Machine ownership is declared in [`Meta/FILEMAP.toml`](Meta/FILEMAP.toml); this list only routes readers to what they will find.

- [`CLAUDE.md`](CLAUDE.md) contains the repository constitution in Chinese.
- [`agents/CONTEXT.md`](agents/CONTEXT.md) contains the compact repository map and workflow.
- [`docs/develop/spec/golden-ledger-repo-spec.md`](docs/develop/spec/golden-ledger-repo-spec.md) contains the repository specification.
- [`D5/`](D5/) contains the Lean formalization.
- [`Blueprint/`](Blueprint/) contains hand-written `.scribe.cs` sources and emitted Markdown. The [mdBook](https://the-omega-institute.github.io/trureturing-mdbook/) is externally built over `Blueprint/**/*.md`; this repository does not verify the hosted deployment's freshness.
- [`docs/develop/theory/`](docs/develop/theory/) contains reference inputs.
- [`Problems/`](Problems/) contains open problems posted for outside attack.
