---
name: omega-math-migration
description: Port existing trureturing Lean formalizations to strict OmegaInit and OmegaMath, migrate their original D5 declarations and callers, and verify mathematical equivalence and zero axiom dependencies before opening a PR.
---

# Strict Omega Math migration

Work in a linked worktree on a coherent group of existing declarations. Read `CLAUDE.md` §3.2 and the library guide before choosing where to put a proof. Read the frozen-state rules in spec A14 before changing a frozen declaration. [Library guide](../../src/README.md) · [Repository specification](../../docs/develop/spec/golden-ledger-repo-spec.md)

1. Fix a baseline commit. Read the old statements, hypotheses, types, definitions and consumers. Record the target declarations and their correspondence in the PR. Prefer a group whose prerequisites and callers can migrate together.
2. Reuse strict library declarations. Put missing reusable constructive mathematics under `src/OmegaMath/` and use `module` and `prelude`. Follow the pinned upstream naming and ownership correspondence for ports. The library depends only on strict Omega libraries. Keep D5 identifiers, paths, GIDs, links and migration notes on the consumer side, including all prose and comments.
3. Edit the original D5 owners to use the strict types and proofs. Update callers, Scribe and Reg where their Lean-facing interfaces change. Use a mixed Lean probe on the consumer side to prove correspondence for all inputs when representations change. Keep any compatibility adapters with their mixed consumers. Record partial ports and exact missing prerequisites in the PR.
4. Build selected strict library and D5 modules, replay the relevant strict closures with `lake test -- <strict-modules>`, and take a scoped report for the migrated D5 declarations. Require `axioms: []` and an explicit, nonempty `libraries` subset of `{OmegaInit, OmegaMath}` for the Omega-only claim. Use the canonical `ledger-align --selector` writer for changed frozen pins and `--refresh-annotations` when remeasuring an unchanged pin. Build affected callers and run applicable repository checks.
5. Check the library source and its guide for D5 references. Report the exact audited scope, semantic comparison, frozen state changes and outstanding work in a focused PR to `dev`. Use PR checks at the published head as the integration result.

```sh
make lean LEAN_TARGETS="OmegaMath.Topic D5.Owner"
make lean-report-scoped LEAN_TARGETS="D5.Owner"
lake test -- OmegaMath.Topic
rg -n '\bD5\b' src/OmegaInit src/OmegaMath src/README.md
```

The search should produce no matches. The library audit checks import closure and kernel replay. The scoped report checks the actual dependencies of each migrated D5 declaration.
