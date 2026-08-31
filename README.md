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
D5/ --projects--> Blueprint/ (derived; no authority)
D5/ --projects--> mdBook (derived; no authority)
```

## The ledger, measured

### measured 2026-08-31 at dev d343b970ac7450641e3697fb310e99e397083eab

| Proof-state evidence | Reading | Exact rerunnable command |
| --- | --- | --- |
| Frozen nodes in the append-only ledger | 2,788, all of `event_type: "Freeze"` (zero `Revoke`, zero `Reattest`), `schema_version: 5` | `ls Golden/Frozen/accepted \| wc -l; python3 -c 'import glob,json; x=[json.load(open(f)) for f in glob.glob("Golden/Frozen/accepted/*.json")]; print(*(sum(y["event_type"]==e for y in x) for e in ("Freeze","Revoke","Reattest")), sorted(set(y["schema_version"] for y in x)))'` |
| Content-addressed prerequisite edges between them | 2,737 (855 roots; max 48 prerequisites on one node) | `python3 -c 'import glob,json; x=[json.load(open(f))["payload"]["prerequisite_frozen_node_ids"] for f in glob.glob("Golden/Frozen/accepted/*.json")]; print(sum(map(len,x)),sum(not y for y in x),max(map(len,x)))'` |
| Declarations carried by those frozen nodes | 26,801 distinct declaration names — **14,461 of kind `theorem`**, 11,238 `def`, 490 `constructor`, 317 `inductive`, 317 `recursor`, 1 `opaque` | `python3 -c 'import collections,glob,json; d=[y for f in glob.glob("Golden/Frozen/accepted/*.json") for y in json.load(open(f))["payload"]["declaration_statement_ids"]]; c=collections.Counter(y["kind"] for y in d); print(len({y["declaration_name_key"] for y in d}),*(c[k] for k in ("theorem","def","constructor","inductive","recursor","opaque")))'` |
| Unproved bodies in `D5/` | exactly **1** `sorry`, at `D5/X_Frontier/Hearts.lean:76` | `grep -rn '^[[:space:]]*sorry[[:space:]]*$' D5 --include='*.lean'` |
| Pinned environment | Lean `v4.31.0`; mathlib `inputRev v4.31.0` | `cat lean-toolchain; jq -r '.packages[] \| select(.name == "mathlib") \| .inputRev' lake-manifest.json` |

The truth DAG is not a metaphor — its nodes and its edges are the committed bytes, and both
are countable.

## The open frontier

[D5/X_Frontier/Hearts.lean](D5/X_Frontier/Hearts.lean) holds exactly two open-heart objects,
and their syntactic asymmetry is the boundary.

- `o5_independence` is a `theorem` whose body is that single `sorry`: it states zero
  localization for the canonical golden Euler germ on the structural line.
- `o6WeilPositivityStatement` is a `def … : Prop`: it names Weil positivity, classically
  equivalent to the Riemann Hypothesis, and asserts no proof, no theorem, and no axiom; a
  `sorry` count cannot see it.

The `sorry` count is 1, while the open hearts are 2; the module's docstring owns the remaining
context.

## Build and verify

`make help` is the single live command entrance and owns the command vocabulary. Of the targets
it names, `make test` is the mathematical gate, while `make preflight` locally pre-verifies the
three checks; preflight is a local preview, not GitHub authority.

This repository defines `engineering`, `lean-inspect`, and `admission` checks. It does not
verify GitHub's required-check or branch-protection configuration, so it makes no claim that
those checks are enforced on every merge.

## Read and navigate

- [`CLAUDE.md`](CLAUDE.md) is the governing constitution in Chinese and is authoritative.
- [`agents/CONTEXT.md`](agents/CONTEXT.md) is authoritative for the compact repository map and
  the Route → Edit → Check workflow.
- [`docs/develop/spec/golden-ledger-repo-spec.md`](docs/develop/spec/golden-ledger-repo-spec.md)
  is the sole normative specification.
- [`D5/`](D5/) is the authoritative Lean source; [`Blueprint/`](Blueprint/) and the
  [mdBook](https://the-omega-institute.github.io/trureturing-mdbook/) are derived reading
  projections rebuilt from this repository and hold no authority over anything here.
- [`docs/develop/theory/`](docs/develop/theory/) contains reference inputs only and is not
  authoritative.
- [`Problems/`](Problems/) is authoritative for open problems posted for outside attack.
