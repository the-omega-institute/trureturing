---
name: atom-retirement
description: Retire completed or canonically settled digestion atoms and archive or delete their theory input in trureturing. Use for cleaning terminal intake sources and the active atom ledger; unresolved propositions and Lean theorem removal use their own routes.
---

# Atom retirement

Use the existing cover and settlement writers to establish completion, then use `make retire-sources` to remove terminal intake units. The normative contract is SPEC §11.21 in `docs/develop/spec/golden-ledger-repo-spec.md`; CLAUDE.md §§1.2, 2.10 and 6.1 govern scope, retained results and the worktree. This skill supplies no new mathematical status.

Work in a compatible linked worktree. Read the selected `source.toml`, atoms and required context. Resolve source selectors through the CLI; never remove YAML by glob or hand-edit status. The cleanup unit is a whole registered source: leaving its input active after deleting a few atoms lets a later ingest recreate them. When only some atoms are terminal, complete the remaining items through [codex-formalize](../codex-formalize/SKILL.md); report the specific outstanding claims if they cannot be completed.

An atom qualifies through one of the existing routes:

- Complete current frozen coverage supports `absorbed-closed` and `Deletable`, including the parent and every descendant.
- `make settle` has established `nonpropositional-inapplicable` for commentary with no proposition or an upstream-only conclusion, using the actual context and a faithful justification.

“Cannot formalize” is not a proof of impossibility and not a settlement category. A conjecture, missing prerequisite, ambiguous meaning, failed proof attempt or exhausted budget remains unresolved. Do not manufacture a settlement to make cleanup succeed. A structural `kind` alone is insufficient. Mixed atoms need decomposition and clause-complete processing first.

Choose archive unless the user requests deletion. The user's authorization persists across preview and write; do not request the same permission again. A request to build this mechanism alone does not authorize a repository-wide cleanup. Run within the user's selected scope:

```sh
make retire-sources SOURCES="<source-id-or-path>" MODE=archive
make retire-sources SOURCES="<source-id-or-path>" MODE=archive WRITE=1
```

Use `MODE=delete` in both commands when deletion is requested. Multiple space-separated sources form one transaction. Make builds the CLI and prepares a scoped current Lean report only when coverage requires it. Direct CLI callers can use `--lean-inputs` to obtain that scope and the existing `STRATALINT_LEAN_REPORT` override to supply its report.

The writer rejects incomplete or stale coverage, unresolved chains, bad CAS, changed input, archive collisions and retained references. It resolves ordinary Markdown destinations and conservatively matches the old path or filename; declared aliases to removed theory or ledger paths also block retirement. Inspect an actual hit before changing anything. Include mutually dependent terminal sources in the same batch, or repair consumers within the authorized scope. If a retained consumer still needs an atom, preserve that atom's source. Never clear a chain or remove a receipt to bypass the rejection. Inputs and references are checked again after archive publication before originals are removed. The writer does not establish the absence of links in external repositories, generated URLs or arbitrary embedded HTML; inspect such consumers when the selected source uses them.

Archive moves the theory Markdown into `docs/develop/archive/theory/`, outside intake and default dispatch, and preserves the referents of ordinary Markdown relative links. Inspect images, reference links and any embedded HTML after relocation. Delete removes the theory original. Both remove the source's active metadata, atom YAML and context pointers; existing immutable CAS supplies shared material and is retained. Existing Lean theorems, Scribe, Reg and frozen membership remain available. Moving or deleting those requires a separate explicit request and dependency-aware change.

After a successful write, inspect the actual diff and report source and atom counts, archive/delete mode, retained blockers and validation exits. Run the applicable required checks. Commit the coherent change using the worktree checkpoint entry. Do not retain process logs, receipts, duplicate metadata snapshots or a new cleanup ledger. History belongs to Git. A preview is not a completed cleanup, writer success is not proof of mathematical truth, and local success is not merged delivery.
